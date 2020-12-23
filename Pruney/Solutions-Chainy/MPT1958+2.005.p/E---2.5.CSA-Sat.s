%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:22 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 139 expanded)
%              Number of clauses        :   34 (  55 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :  285 (1011 expanded)
%              Number of equality atoms :   31 ( 133 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(t45_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_yellow_0)).

fof(dt_k4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_0)).

fof(t5_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( v7_struct_0(X1)
      <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_waybel_7)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(cc4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_yellow_0(X1)
       => ( v1_yellow_0(X1)
          & v2_yellow_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_11,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r2_lattice3(X11,X12,X13)
        | X13 != k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_lattice3(X11,X12,X14)
        | r1_orders_2(X11,X13,X14)
        | X13 != k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X11))
        | ~ r2_lattice3(X11,X12,X13)
        | X13 = k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( r2_lattice3(X11,X12,esk1_3(X11,X12,X13))
        | ~ r2_lattice3(X11,X12,X13)
        | X13 = k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,X13,esk1_3(X11,X12,X13))
        | ~ r2_lattice3(X11,X12,X13)
        | X13 = k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_12,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_13,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | k3_yellow_0(X10) = k1_yellow_0(X10,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_14,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | m1_subset_1(k3_yellow_0(X16),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

fof(c_0_15,plain,(
    ! [X21,X22] :
      ( ( r2_lattice3(X21,k1_xboole_0,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( r1_lattice3(X21,k1_xboole_0,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] :
      ( ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ r1_orders_2(X6,X7,X8)
      | ~ r1_orders_2(X6,X8,X7)
      | X7 = X8 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_17,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_18,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_19,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_20,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_21,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_22,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_23,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),
    [final]).

fof(c_0_25,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v5_orders_2(X19)
      | ~ v2_yellow_0(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | r1_orders_2(X19,X20,k4_yellow_0(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).

fof(c_0_26,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | m1_subset_1(k4_yellow_0(X17),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_yellow_0(X1)
          & l1_orders_2(X1) )
       => ( v7_struct_0(X1)
        <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t5_waybel_7])).

cnf(c_0_28,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | ~ r2_lattice3(X1,X2,esk1_3(X1,X3,k1_yellow_0(X1,X2)))
    | ~ r2_lattice3(X1,X3,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_22]),
    [final]).

cnf(c_0_29,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,k1_yellow_0(X2,X3))
    | ~ m1_subset_1(k1_yellow_0(X2,X3),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17]),
    [final]).

cnf(c_0_30,plain,
    ( k1_yellow_0(X1,X2) = k3_yellow_0(X1)
    | ~ r2_lattice3(X1,X2,k3_yellow_0(X1))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(esk1_3(X1,X2,k3_yellow_0(X1)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_24]),c_0_19])).

cnf(c_0_31,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_33,plain,
    ( m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

fof(c_0_34,plain,(
    ! [X18] :
      ( ( r1_yellow_0(X18,k1_xboole_0)
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v1_yellow_0(X18)
        | ~ l1_orders_2(X18) )
      & ( r2_yellow_0(X18,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v5_orders_2(X18)
        | ~ v1_yellow_0(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

fof(c_0_35,plain,(
    ! [X9] :
      ( ( v1_yellow_0(X9)
        | ~ v3_yellow_0(X9)
        | ~ l1_orders_2(X9) )
      & ( v2_yellow_0(X9)
        | ~ v3_yellow_0(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).

fof(c_0_36,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v5_orders_2(esk2_0)
    & v3_yellow_0(esk2_0)
    & l1_orders_2(esk2_0)
    & ( ~ v7_struct_0(esk2_0)
      | k4_yellow_0(esk2_0) != k3_yellow_0(esk2_0) )
    & ( v7_struct_0(esk2_0)
      | k4_yellow_0(esk2_0) = k3_yellow_0(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).

cnf(c_0_38,plain,
    ( k1_yellow_0(X1,k1_xboole_0) = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,k1_xboole_0))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(k1_yellow_0(X1,k1_xboole_0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_22]),
    [final]).

cnf(c_0_39,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | ~ r2_lattice3(X1,X3,k1_yellow_0(X1,X2))
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ r1_yellow_0(X1,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_17]),
    [final]).

cnf(c_0_40,plain,
    ( k1_yellow_0(X1,X2) = k3_yellow_0(X1)
    | ~ r2_lattice3(X1,X2,k3_yellow_0(X1))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_19]),
    [final]).

cnf(c_0_41,plain,
    ( X1 = k3_yellow_0(X2)
    | ~ r1_yellow_0(X2,k1_xboole_0)
    | ~ r1_orders_2(X2,X1,k3_yellow_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19]),
    [final]).

cnf(c_0_42,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_43,plain,
    ( k4_yellow_0(X1) = X2
    | v2_struct_0(X1)
    | ~ v2_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_32]),c_0_33]),
    [final]).

cnf(c_0_44,plain,
    ( r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_45,plain,
    ( r2_yellow_0(X1,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34]),
    [final]).

cnf(c_0_46,plain,
    ( r1_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_47,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34]),
    [final]).

cnf(c_0_48,plain,
    ( v2_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_49,plain,
    ( v1_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | k4_yellow_0(esk2_0) = k3_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( ~ v7_struct_0(esk2_0)
    | k4_yellow_0(esk2_0) != k3_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( v3_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:40:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.048 s
% 0.19/0.39  
% 0.19/0.39  # No proof found!
% 0.19/0.39  # SZS status CounterSatisfiable
% 0.19/0.39  # SZS output start Saturation
% 0.19/0.39  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.19/0.39  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.19/0.39  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.19/0.39  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.19/0.39  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 0.19/0.39  fof(t45_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,k4_yellow_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_yellow_0)).
% 0.19/0.39  fof(dt_k4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_yellow_0)).
% 0.19/0.39  fof(t5_waybel_7, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_waybel_7)).
% 0.19/0.39  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.19/0.39  fof(cc4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>(v3_yellow_0(X1)=>(v1_yellow_0(X1)&v2_yellow_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_yellow_0)).
% 0.19/0.39  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.39  fof(c_0_11, plain, ![X11, X12, X13, X14]:(((r2_lattice3(X11,X12,X13)|X13!=k1_yellow_0(X11,X12)|~r1_yellow_0(X11,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_lattice3(X11,X12,X14)|r1_orders_2(X11,X13,X14))|X13!=k1_yellow_0(X11,X12)|~r1_yellow_0(X11,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11)))&((m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X11))|~r2_lattice3(X11,X12,X13)|X13=k1_yellow_0(X11,X12)|~r1_yellow_0(X11,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&((r2_lattice3(X11,X12,esk1_3(X11,X12,X13))|~r2_lattice3(X11,X12,X13)|X13=k1_yellow_0(X11,X12)|~r1_yellow_0(X11,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&(~r1_orders_2(X11,X13,esk1_3(X11,X12,X13))|~r2_lattice3(X11,X12,X13)|X13=k1_yellow_0(X11,X12)|~r1_yellow_0(X11,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.19/0.39  cnf(c_0_12, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  fof(c_0_13, plain, ![X10]:(~l1_orders_2(X10)|k3_yellow_0(X10)=k1_yellow_0(X10,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.19/0.39  fof(c_0_14, plain, ![X16]:(~l1_orders_2(X16)|m1_subset_1(k3_yellow_0(X16),u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.19/0.39  fof(c_0_15, plain, ![X21, X22]:((r2_lattice3(X21,k1_xboole_0,X22)|~m1_subset_1(X22,u1_struct_0(X21))|~l1_orders_2(X21))&(r1_lattice3(X21,k1_xboole_0,X22)|~m1_subset_1(X22,u1_struct_0(X21))|~l1_orders_2(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.19/0.39  fof(c_0_16, plain, ![X6, X7, X8]:(~v5_orders_2(X6)|~l1_orders_2(X6)|(~m1_subset_1(X7,u1_struct_0(X6))|(~m1_subset_1(X8,u1_struct_0(X6))|(~r1_orders_2(X6,X7,X8)|~r1_orders_2(X6,X8,X7)|X7=X8)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.19/0.39  cnf(c_0_17, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_12]), ['final']).
% 0.19/0.39  cnf(c_0_18, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.19/0.39  cnf(c_0_19, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.19/0.39  cnf(c_0_20, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.19/0.39  cnf(c_0_21, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.19/0.39  cnf(c_0_22, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.19/0.39  cnf(c_0_23, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.19/0.39  cnf(c_0_24, plain, (r1_orders_2(X1,k3_yellow_0(X1),X2)|~r1_yellow_0(X1,k1_xboole_0)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), ['final']).
% 0.19/0.39  fof(c_0_25, plain, ![X19, X20]:(v2_struct_0(X19)|~v5_orders_2(X19)|~v2_yellow_0(X19)|~l1_orders_2(X19)|(~m1_subset_1(X20,u1_struct_0(X19))|r1_orders_2(X19,X20,k4_yellow_0(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).
% 0.19/0.39  fof(c_0_26, plain, ![X17]:(~l1_orders_2(X17)|m1_subset_1(k4_yellow_0(X17),u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).
% 0.19/0.39  fof(c_0_27, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1)))), inference(assume_negation,[status(cth)],[t5_waybel_7])).
% 0.19/0.39  cnf(c_0_28, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|~r2_lattice3(X1,X2,esk1_3(X1,X3,k1_yellow_0(X1,X2)))|~r2_lattice3(X1,X3,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_22]), ['final']).
% 0.19/0.39  cnf(c_0_29, plain, (X1=k1_yellow_0(X2,X3)|~r2_lattice3(X2,X3,X1)|~r1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,k1_yellow_0(X2,X3))|~m1_subset_1(k1_yellow_0(X2,X3),u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_23, c_0_17]), ['final']).
% 0.19/0.39  cnf(c_0_30, plain, (k1_yellow_0(X1,X2)=k3_yellow_0(X1)|~r2_lattice3(X1,X2,k3_yellow_0(X1))|~r1_yellow_0(X1,k1_xboole_0)|~r1_yellow_0(X1,X2)|~m1_subset_1(esk1_3(X1,X2,k3_yellow_0(X1)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_24]), c_0_19])).
% 0.19/0.39  cnf(c_0_31, plain, (r2_lattice3(X1,X2,X3)|X3!=k1_yellow_0(X1,X2)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_32, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,k4_yellow_0(X1))|~v5_orders_2(X1)|~v2_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.19/0.39  cnf(c_0_33, plain, (m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.19/0.39  fof(c_0_34, plain, ![X18]:((r1_yellow_0(X18,k1_xboole_0)|(v2_struct_0(X18)|~v5_orders_2(X18)|~v1_yellow_0(X18)|~l1_orders_2(X18)))&(r2_yellow_0(X18,u1_struct_0(X18))|(v2_struct_0(X18)|~v5_orders_2(X18)|~v1_yellow_0(X18)|~l1_orders_2(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.19/0.39  fof(c_0_35, plain, ![X9]:((v1_yellow_0(X9)|~v3_yellow_0(X9)|~l1_orders_2(X9))&(v2_yellow_0(X9)|~v3_yellow_0(X9)|~l1_orders_2(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).
% 0.19/0.39  fof(c_0_36, plain, ![X5]:(~l1_orders_2(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.39  fof(c_0_37, negated_conjecture, ((((~v2_struct_0(esk2_0)&v5_orders_2(esk2_0))&v3_yellow_0(esk2_0))&l1_orders_2(esk2_0))&((~v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)!=k3_yellow_0(esk2_0))&(v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)=k3_yellow_0(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).
% 0.19/0.39  cnf(c_0_38, plain, (k1_yellow_0(X1,k1_xboole_0)=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,k1_yellow_0(X1,k1_xboole_0))|~r1_yellow_0(X1,k1_xboole_0)|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,k1_xboole_0),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_22]), ['final']).
% 0.19/0.39  cnf(c_0_39, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|~r2_lattice3(X1,X3,k1_yellow_0(X1,X2))|~r2_lattice3(X1,X2,k1_yellow_0(X1,X3))|~r1_yellow_0(X1,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_29, c_0_17]), ['final']).
% 0.19/0.39  cnf(c_0_40, plain, (k1_yellow_0(X1,X2)=k3_yellow_0(X1)|~r2_lattice3(X1,X2,k3_yellow_0(X1))|~r1_yellow_0(X1,k1_xboole_0)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_22]), c_0_19]), ['final']).
% 0.19/0.39  cnf(c_0_41, plain, (X1=k3_yellow_0(X2)|~r1_yellow_0(X2,k1_xboole_0)|~r1_orders_2(X2,X1,k3_yellow_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_19]), ['final']).
% 0.19/0.39  cnf(c_0_42, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_31]), ['final']).
% 0.19/0.39  cnf(c_0_43, plain, (k4_yellow_0(X1)=X2|v2_struct_0(X1)|~v2_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_32]), c_0_33]), ['final']).
% 0.19/0.39  cnf(c_0_44, plain, (r2_lattice3(X1,X2,esk1_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.19/0.39  cnf(c_0_45, plain, (r2_yellow_0(X1,u1_struct_0(X1))|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34]), ['final']).
% 0.19/0.39  cnf(c_0_46, plain, (r1_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.19/0.39  cnf(c_0_47, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_34]), ['final']).
% 0.19/0.39  cnf(c_0_48, plain, (v2_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.39  cnf(c_0_49, plain, (v1_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.39  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)=k3_yellow_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (~v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)!=k3_yellow_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (v3_yellow_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.19/0.39  # SZS output end Saturation
% 0.19/0.39  # Proof object total steps             : 57
% 0.19/0.39  # Proof object clause steps            : 34
% 0.19/0.39  # Proof object formula steps           : 23
% 0.19/0.39  # Proof object conjectures             : 9
% 0.19/0.39  # Proof object clause conjectures      : 6
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 23
% 0.19/0.39  # Proof object initial formulas used   : 11
% 0.19/0.39  # Proof object generating inferences   : 9
% 0.19/0.39  # Proof object simplifying inferences  : 10
% 0.19/0.39  # Parsed axioms                        : 11
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 23
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 23
% 0.19/0.39  # Processed clauses                    : 44
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 8
% 0.19/0.39  # ...remaining for further processing  : 36
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 3
% 0.19/0.39  # Backward-rewritten                   : 0
% 0.19/0.39  # Generated clauses                    : 22
% 0.19/0.39  # ...of the previous two non-trivial   : 21
% 0.19/0.39  # Contextual simplify-reflections      : 9
% 0.19/0.39  # Paramodulations                      : 20
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 2
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
% 0.19/0.39  # Current number of processed clauses  : 31
% 0.19/0.39  #    Positive orientable unit clauses  : 3
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 27
% 0.19/0.39  # Current number of unprocessed clauses: 0
% 0.19/0.39  # ...number of literals in the above   : 0
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 3
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 474
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 42
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 20
% 0.19/0.39  # Unit Clause-clause subsumption calls : 0
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 0
% 0.19/0.39  # BW rewrite match successes           : 0
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 2896
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.053 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.057 s
% 0.19/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
