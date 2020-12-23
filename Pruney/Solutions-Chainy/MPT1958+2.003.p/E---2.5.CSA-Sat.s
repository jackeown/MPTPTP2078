%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:22 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 140 expanded)
%              Number of clauses        :   35 (  56 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  291 (1058 expanded)
%              Number of equality atoms :   32 ( 142 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_yellow_0(X1,X2)
           => ( X3 = k2_yellow_0(X1,X2)
            <=> ( r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(d12_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).

fof(dt_k4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_0)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(t44_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(t5_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( v7_struct_0(X1)
      <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_waybel_7)).

fof(t43_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r2_yellow_0(X1,k1_xboole_0)
        & r1_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_yellow_0)).

fof(cc4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_yellow_0(X1)
       => ( v1_yellow_0(X1)
          & v2_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13] :
      ( ( r1_lattice3(X10,X11,X12)
        | X12 != k2_yellow_0(X10,X11)
        | ~ r2_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_lattice3(X10,X11,X13)
        | r1_orders_2(X10,X13,X12)
        | X12 != k2_yellow_0(X10,X11)
        | ~ r2_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X12),u1_struct_0(X10))
        | ~ r1_lattice3(X10,X11,X12)
        | X12 = k2_yellow_0(X10,X11)
        | ~ r2_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r1_lattice3(X10,X11,esk1_3(X10,X11,X12))
        | ~ r1_lattice3(X10,X11,X12)
        | X12 = k2_yellow_0(X10,X11)
        | ~ r2_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk1_3(X10,X11,X12),X12)
        | ~ r1_lattice3(X10,X11,X12)
        | X12 = k2_yellow_0(X10,X11)
        | ~ r2_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

cnf(c_0_12,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_13,plain,
    ( X3 = k2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_14,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ m1_subset_1(k2_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_15,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_16,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | k4_yellow_0(X15) = k2_yellow_0(X15,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).

fof(c_0_17,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | m1_subset_1(k4_yellow_0(X17),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).

fof(c_0_18,plain,(
    ! [X6,X7,X8] :
      ( ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ r1_orders_2(X6,X7,X8)
      | ~ r1_orders_2(X6,X8,X7)
      | X7 = X8 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_19,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X3,k2_yellow_0(X1,X2)))
    | ~ r1_lattice3(X1,X3,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),
    [final]).

cnf(c_0_20,plain,
    ( k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_21,plain,
    ( m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

fof(c_0_22,plain,(
    ! [X21,X22] :
      ( ( r2_lattice3(X21,k1_xboole_0,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( r1_lattice3(X21,k1_xboole_0,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

cnf(c_0_23,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_24,plain,
    ( k2_yellow_0(X1,X2) = k4_yellow_0(X1)
    | ~ r1_lattice3(X1,k1_xboole_0,esk1_3(X1,X2,k4_yellow_0(X1)))
    | ~ r1_lattice3(X1,X2,k4_yellow_0(X1))
    | ~ r2_yellow_0(X1,k1_xboole_0)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( r1_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

fof(c_0_26,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v5_orders_2(X19)
      | ~ v1_yellow_0(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | r1_orders_2(X19,k3_yellow_0(X19),X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

fof(c_0_27,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | m1_subset_1(k3_yellow_0(X16),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_yellow_0(X1)
          & l1_orders_2(X1) )
       => ( v7_struct_0(X1)
        <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t5_waybel_7])).

cnf(c_0_29,plain,
    ( k2_yellow_0(X1,X2) = X3
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X2),X3)
    | ~ m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14]),
    [final]).

cnf(c_0_30,plain,
    ( k2_yellow_0(X1,X2) = k4_yellow_0(X1)
    | ~ r1_lattice3(X1,X2,k4_yellow_0(X1))
    | ~ r2_yellow_0(X1,k1_xboole_0)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(esk1_3(X1,X2,k4_yellow_0(X1)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X2,k4_yellow_0(X1))
    | ~ r2_yellow_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_20]),c_0_21]),c_0_25]),
    [final]).

cnf(c_0_32,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_34,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

fof(c_0_35,plain,(
    ! [X18] :
      ( ( r2_yellow_0(X18,k1_xboole_0)
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_yellow_0(X18)
        | ~ l1_orders_2(X18) )
      & ( r1_yellow_0(X18,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v2_yellow_0(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_yellow_0])])])])).

fof(c_0_36,plain,(
    ! [X9] :
      ( ( v1_yellow_0(X9)
        | ~ v3_yellow_0(X9)
        | ~ l1_orders_2(X9) )
      & ( v2_yellow_0(X9)
        | ~ v3_yellow_0(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).

fof(c_0_37,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v5_orders_2(esk2_0)
    & v3_yellow_0(esk2_0)
    & l1_orders_2(esk2_0)
    & ( ~ v7_struct_0(esk2_0)
      | k4_yellow_0(esk2_0) != k3_yellow_0(esk2_0) )
    & ( v7_struct_0(esk2_0)
      | k4_yellow_0(esk2_0) = k3_yellow_0(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).

cnf(c_0_39,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X2,k2_yellow_0(X1,X3))
    | ~ r1_lattice3(X1,X3,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(k2_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_14]),
    [final]).

cnf(c_0_40,plain,
    ( k2_yellow_0(X1,k1_xboole_0) = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,k2_yellow_0(X1,k1_xboole_0))
    | ~ r2_yellow_0(X1,k1_xboole_0)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(k2_yellow_0(X1,k1_xboole_0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_25]),c_0_15]),
    [final]).

cnf(c_0_41,plain,
    ( k2_yellow_0(X1,X2) = k4_yellow_0(X1)
    | ~ r1_lattice3(X1,X2,k4_yellow_0(X1))
    | ~ r2_yellow_0(X1,k1_xboole_0)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_15]),c_0_21]),
    [final]).

cnf(c_0_42,plain,
    ( k4_yellow_0(X1) = X2
    | ~ r2_yellow_0(X1,k1_xboole_0)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_31]),c_0_21]),
    [final]).

cnf(c_0_43,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_44,plain,
    ( X1 = k3_yellow_0(X2)
    | v2_struct_0(X2)
    | ~ v1_yellow_0(X2)
    | ~ r1_orders_2(X2,X1,k3_yellow_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_33]),c_0_34]),
    [final]).

cnf(c_0_45,plain,
    ( r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_46,plain,
    ( r1_yellow_0(X1,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_47,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_48,plain,
    ( r2_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_49,plain,
    ( v2_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_50,plain,
    ( v1_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_51,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | k4_yellow_0(esk2_0) = k3_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( ~ v7_struct_0(esk2_0)
    | k4_yellow_0(esk2_0) != k3_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( v3_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:25:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(d10_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_yellow_0(X1,X2)=>(X3=k2_yellow_0(X1,X2)<=>(r1_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_yellow_0)).
% 0.14/0.38  fof(d12_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k4_yellow_0(X1)=k2_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_yellow_0)).
% 0.14/0.38  fof(dt_k4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_yellow_0)).
% 0.14/0.38  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_orders_2)).
% 0.14/0.38  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.14/0.38  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.14/0.38  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.14/0.38  fof(t5_waybel_7, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_waybel_7)).
% 0.14/0.38  fof(t43_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>(r2_yellow_0(X1,k1_xboole_0)&r1_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_yellow_0)).
% 0.14/0.38  fof(cc4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>(v3_yellow_0(X1)=>(v1_yellow_0(X1)&v2_yellow_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_0)).
% 0.14/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.38  fof(c_0_11, plain, ![X10, X11, X12, X13]:(((r1_lattice3(X10,X11,X12)|X12!=k2_yellow_0(X10,X11)|~r2_yellow_0(X10,X11)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&(~m1_subset_1(X13,u1_struct_0(X10))|(~r1_lattice3(X10,X11,X13)|r1_orders_2(X10,X13,X12))|X12!=k2_yellow_0(X10,X11)|~r2_yellow_0(X10,X11)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10)))&((m1_subset_1(esk1_3(X10,X11,X12),u1_struct_0(X10))|~r1_lattice3(X10,X11,X12)|X12=k2_yellow_0(X10,X11)|~r2_yellow_0(X10,X11)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&((r1_lattice3(X10,X11,esk1_3(X10,X11,X12))|~r1_lattice3(X10,X11,X12)|X12=k2_yellow_0(X10,X11)|~r2_yellow_0(X10,X11)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&(~r1_orders_2(X10,esk1_3(X10,X11,X12),X12)|~r1_lattice3(X10,X11,X12)|X12=k2_yellow_0(X10,X11)|~r2_yellow_0(X10,X11)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).
% 0.14/0.38  cnf(c_0_12, plain, (r1_orders_2(X2,X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_13, plain, (X3=k2_yellow_0(X1,X2)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_14, plain, (r1_orders_2(X1,X2,k2_yellow_0(X1,X3))|~r1_lattice3(X1,X3,X2)|~r2_yellow_0(X1,X3)|~m1_subset_1(k2_yellow_0(X1,X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_15, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X3=k2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.38  fof(c_0_16, plain, ![X15]:(~l1_orders_2(X15)|k4_yellow_0(X15)=k2_yellow_0(X15,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).
% 0.14/0.38  fof(c_0_17, plain, ![X17]:(~l1_orders_2(X17)|m1_subset_1(k4_yellow_0(X17),u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).
% 0.14/0.38  fof(c_0_18, plain, ![X6, X7, X8]:(~v5_orders_2(X6)|~l1_orders_2(X6)|(~m1_subset_1(X7,u1_struct_0(X6))|(~m1_subset_1(X8,u1_struct_0(X6))|(~r1_orders_2(X6,X7,X8)|~r1_orders_2(X6,X8,X7)|X7=X8)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.14/0.38  cnf(c_0_19, plain, (k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|~r1_lattice3(X1,X2,esk1_3(X1,X3,k2_yellow_0(X1,X2)))|~r1_lattice3(X1,X3,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X3)|~r2_yellow_0(X1,X2)|~m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_20, plain, (k4_yellow_0(X1)=k2_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.38  cnf(c_0_21, plain, (m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.38  fof(c_0_22, plain, ![X21, X22]:((r2_lattice3(X21,k1_xboole_0,X22)|~m1_subset_1(X22,u1_struct_0(X21))|~l1_orders_2(X21))&(r1_lattice3(X21,k1_xboole_0,X22)|~m1_subset_1(X22,u1_struct_0(X21))|~l1_orders_2(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.14/0.38  cnf(c_0_23, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_24, plain, (k2_yellow_0(X1,X2)=k4_yellow_0(X1)|~r1_lattice3(X1,k1_xboole_0,esk1_3(X1,X2,k4_yellow_0(X1)))|~r1_lattice3(X1,X2,k4_yellow_0(X1))|~r2_yellow_0(X1,k1_xboole_0)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.14/0.38  cnf(c_0_25, plain, (r1_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.38  fof(c_0_26, plain, ![X19, X20]:(v2_struct_0(X19)|~v5_orders_2(X19)|~v1_yellow_0(X19)|~l1_orders_2(X19)|(~m1_subset_1(X20,u1_struct_0(X19))|r1_orders_2(X19,k3_yellow_0(X19),X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.14/0.38  fof(c_0_27, plain, ![X16]:(~l1_orders_2(X16)|m1_subset_1(k3_yellow_0(X16),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.14/0.38  fof(c_0_28, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1)))), inference(assume_negation,[status(cth)],[t5_waybel_7])).
% 0.14/0.38  cnf(c_0_29, plain, (k2_yellow_0(X1,X2)=X3|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X2)|~r1_orders_2(X1,k2_yellow_0(X1,X2),X3)|~m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_23, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_30, plain, (k2_yellow_0(X1,X2)=k4_yellow_0(X1)|~r1_lattice3(X1,X2,k4_yellow_0(X1))|~r2_yellow_0(X1,k1_xboole_0)|~r2_yellow_0(X1,X2)|~m1_subset_1(esk1_3(X1,X2,k4_yellow_0(X1)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.38  cnf(c_0_31, plain, (r1_orders_2(X1,X2,k4_yellow_0(X1))|~r2_yellow_0(X1,k1_xboole_0)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_20]), c_0_21]), c_0_25]), ['final']).
% 0.14/0.38  cnf(c_0_32, plain, (r1_lattice3(X1,X2,X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_33, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.14/0.38  cnf(c_0_34, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.14/0.38  fof(c_0_35, plain, ![X18]:((r2_yellow_0(X18,k1_xboole_0)|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_yellow_0(X18)|~l1_orders_2(X18)))&(r1_yellow_0(X18,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v2_yellow_0(X18)|~l1_orders_2(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_yellow_0])])])])).
% 0.14/0.38  fof(c_0_36, plain, ![X9]:((v1_yellow_0(X9)|~v3_yellow_0(X9)|~l1_orders_2(X9))&(v2_yellow_0(X9)|~v3_yellow_0(X9)|~l1_orders_2(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).
% 0.14/0.38  fof(c_0_37, plain, ![X5]:(~l1_orders_2(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.38  fof(c_0_38, negated_conjecture, ((((~v2_struct_0(esk2_0)&v5_orders_2(esk2_0))&v3_yellow_0(esk2_0))&l1_orders_2(esk2_0))&((~v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)!=k3_yellow_0(esk2_0))&(v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)=k3_yellow_0(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).
% 0.14/0.38  cnf(c_0_39, plain, (k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|~r1_lattice3(X1,X2,k2_yellow_0(X1,X3))|~r1_lattice3(X1,X3,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X2)|~r2_yellow_0(X1,X3)|~m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(k2_yellow_0(X1,X3),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_29, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_40, plain, (k2_yellow_0(X1,k1_xboole_0)=k2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,k2_yellow_0(X1,k1_xboole_0))|~r2_yellow_0(X1,k1_xboole_0)|~r2_yellow_0(X1,X2)|~m1_subset_1(k2_yellow_0(X1,k1_xboole_0),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_25]), c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_41, plain, (k2_yellow_0(X1,X2)=k4_yellow_0(X1)|~r1_lattice3(X1,X2,k4_yellow_0(X1))|~r2_yellow_0(X1,k1_xboole_0)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_15]), c_0_21]), ['final']).
% 0.14/0.38  cnf(c_0_42, plain, (k4_yellow_0(X1)=X2|~r2_yellow_0(X1,k1_xboole_0)|~r1_orders_2(X1,k4_yellow_0(X1),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_31]), c_0_21]), ['final']).
% 0.14/0.38  cnf(c_0_43, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X2)|~m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_32]), ['final']).
% 0.14/0.38  cnf(c_0_44, plain, (X1=k3_yellow_0(X2)|v2_struct_0(X2)|~v1_yellow_0(X2)|~r1_orders_2(X2,X1,k3_yellow_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_33]), c_0_34]), ['final']).
% 0.14/0.38  cnf(c_0_45, plain, (r1_lattice3(X1,X2,esk1_3(X1,X2,X3))|X3=k2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,X3)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_46, plain, (r1_yellow_0(X1,u1_struct_0(X1))|v2_struct_0(X1)|~v5_orders_2(X1)|~v2_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.14/0.38  cnf(c_0_47, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.38  cnf(c_0_48, plain, (r2_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v2_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.14/0.38  cnf(c_0_49, plain, (v2_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.14/0.38  cnf(c_0_50, plain, (v1_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.14/0.38  cnf(c_0_51, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)=k3_yellow_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (~v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)!=k3_yellow_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (v3_yellow_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 58
% 0.14/0.38  # Proof object clause steps            : 35
% 0.14/0.38  # Proof object formula steps           : 23
% 0.14/0.38  # Proof object conjectures             : 9
% 0.14/0.38  # Proof object clause conjectures      : 6
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 23
% 0.14/0.38  # Proof object initial formulas used   : 11
% 0.14/0.38  # Proof object generating inferences   : 10
% 0.14/0.38  # Proof object simplifying inferences  : 10
% 0.14/0.38  # Parsed axioms                        : 11
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 23
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 23
% 0.14/0.38  # Processed clauses                    : 45
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 9
% 0.14/0.38  # ...remaining for further processing  : 36
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 3
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 23
% 0.14/0.38  # ...of the previous two non-trivial   : 22
% 0.14/0.38  # Contextual simplify-reflections      : 9
% 0.14/0.38  # Paramodulations                      : 21
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 31
% 0.14/0.38  #    Positive orientable unit clauses  : 3
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 27
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 3
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 482
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 46
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 21
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2856
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
