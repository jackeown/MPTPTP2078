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
% Statistics : Number of formulae       :   64 ( 188 expanded)
%              Number of clauses        :   41 (  76 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :    6
%              Number of atoms          :  359 (2014 expanded)
%              Number of equality atoms :   32 ( 206 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

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
    ! [X13,X14,X15,X16,X17] :
      ( ( r2_lattice3(X13,X15,X14)
        | X14 != k1_yellow_0(X13,X15)
        | ~ r1_yellow_0(X13,X15)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X15,X16)
        | r1_orders_2(X13,X14,X16)
        | X14 != k1_yellow_0(X13,X15)
        | ~ r1_yellow_0(X13,X15)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( X14 = k1_yellow_0(X13,X17)
        | m1_subset_1(esk1_3(X13,X14,X17),u1_struct_0(X13))
        | ~ r2_lattice3(X13,X17,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( r1_yellow_0(X13,X17)
        | m1_subset_1(esk1_3(X13,X14,X17),u1_struct_0(X13))
        | ~ r2_lattice3(X13,X17,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( X14 = k1_yellow_0(X13,X17)
        | r2_lattice3(X13,X17,esk1_3(X13,X14,X17))
        | ~ r2_lattice3(X13,X17,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( r1_yellow_0(X13,X17)
        | r2_lattice3(X13,X17,esk1_3(X13,X14,X17))
        | ~ r2_lattice3(X13,X17,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( X14 = k1_yellow_0(X13,X17)
        | ~ r1_orders_2(X13,X14,esk1_3(X13,X14,X17))
        | ~ r2_lattice3(X13,X17,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( r1_yellow_0(X13,X17)
        | ~ r1_orders_2(X13,X14,esk1_3(X13,X14,X17))
        | ~ r2_lattice3(X13,X17,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

cnf(c_0_12,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_13,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | k3_yellow_0(X10) = k1_yellow_0(X10,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_14,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | m1_subset_1(k3_yellow_0(X11),u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ( r2_lattice3(X22,k1_xboole_0,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r1_lattice3(X22,k1_xboole_0,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
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
    | ~ v5_orders_2(X1)
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
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk1_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_22,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
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
    ( r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk1_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_25,plain,
    ( r1_yellow_0(X1,X2)
    | m1_subset_1(esk1_3(X1,X3,X2),u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),
    [final]).

fof(c_0_27,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v5_orders_2(X20)
      | ~ v2_yellow_0(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | r1_orders_2(X20,X21,k4_yellow_0(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).

fof(c_0_28,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(k4_yellow_0(X12),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_yellow_0(X1)
          & l1_orders_2(X1) )
       => ( v7_struct_0(X1)
        <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t5_waybel_7])).

cnf(c_0_30,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | ~ r2_lattice3(X1,X2,esk1_3(X1,k1_yellow_0(X1,X2),X3))
    | ~ r2_lattice3(X1,X3,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_22]),
    [final]).

cnf(c_0_31,plain,
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

cnf(c_0_32,plain,
    ( r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X3,esk1_3(X1,k1_yellow_0(X1,X3),X2))
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_25]),
    [final]).

cnf(c_0_33,plain,
    ( k1_yellow_0(X1,X2) = k3_yellow_0(X1)
    | ~ r2_lattice3(X1,X2,k3_yellow_0(X1))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ m1_subset_1(esk1_3(X1,k3_yellow_0(X1),X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_26]),c_0_19])).

cnf(c_0_34,plain,
    ( r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,k3_yellow_0(X1))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ m1_subset_1(esk1_3(X1,k3_yellow_0(X1),X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_26]),c_0_19])).

cnf(c_0_35,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_37,plain,
    ( m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28]),
    [final]).

fof(c_0_38,plain,(
    ! [X19] :
      ( ( r1_yellow_0(X19,k1_xboole_0)
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v1_yellow_0(X19)
        | ~ l1_orders_2(X19) )
      & ( r2_yellow_0(X19,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v1_yellow_0(X19)
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

fof(c_0_39,plain,(
    ! [X9] :
      ( ( v1_yellow_0(X9)
        | ~ v3_yellow_0(X9)
        | ~ l1_orders_2(X9) )
      & ( v2_yellow_0(X9)
        | ~ v3_yellow_0(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).

fof(c_0_40,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v5_orders_2(esk2_0)
    & v3_yellow_0(esk2_0)
    & l1_orders_2(esk2_0)
    & ( ~ v7_struct_0(esk2_0)
      | k4_yellow_0(esk2_0) != k3_yellow_0(esk2_0) )
    & ( v7_struct_0(esk2_0)
      | k4_yellow_0(esk2_0) = k3_yellow_0(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).

cnf(c_0_42,plain,
    ( k1_yellow_0(X1,k1_xboole_0) = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,k1_xboole_0))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ m1_subset_1(k1_yellow_0(X1,k1_xboole_0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_22]),
    [final]).

cnf(c_0_43,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | ~ r2_lattice3(X1,X3,k1_yellow_0(X1,X2))
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ r1_yellow_0(X1,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_17]),
    [final]).

cnf(c_0_44,plain,
    ( r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,k1_xboole_0))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ m1_subset_1(k1_yellow_0(X1,k1_xboole_0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_25]),
    [final]).

cnf(c_0_45,plain,
    ( k1_yellow_0(X1,X2) = k3_yellow_0(X1)
    | ~ r2_lattice3(X1,X2,k3_yellow_0(X1))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_19]),
    [final]).

cnf(c_0_46,plain,
    ( r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,k3_yellow_0(X1))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_19]),
    [final]).

cnf(c_0_47,plain,
    ( X1 = k3_yellow_0(X2)
    | ~ r1_yellow_0(X2,k1_xboole_0)
    | ~ r1_orders_2(X2,X1,k3_yellow_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_26]),c_0_19]),
    [final]).

cnf(c_0_48,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_49,plain,
    ( k4_yellow_0(X1) = X2
    | v2_struct_0(X1)
    | ~ v2_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_36]),c_0_37]),
    [final]).

cnf(c_0_50,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk1_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_51,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk1_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_52,plain,
    ( r2_yellow_0(X1,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_53,plain,
    ( r1_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_54,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_55,plain,
    ( v2_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_56,plain,
    ( v1_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_57,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | k4_yellow_0(esk2_0) = k3_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( ~ v7_struct_0(esk2_0)
    | k4_yellow_0(esk2_0) != k3_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( v3_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.14/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.028 s
% 0.14/0.37  
% 0.14/0.37  # No proof found!
% 0.14/0.37  # SZS status CounterSatisfiable
% 0.14/0.37  # SZS output start Saturation
% 0.14/0.37  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.14/0.37  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.14/0.37  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.14/0.37  fof(t6_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.14/0.37  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 0.14/0.37  fof(t45_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,k4_yellow_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_yellow_0)).
% 0.14/0.37  fof(dt_k4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_yellow_0)).
% 0.14/0.37  fof(t5_waybel_7, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_waybel_7)).
% 0.14/0.37  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.14/0.37  fof(cc4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>(v3_yellow_0(X1)=>(v1_yellow_0(X1)&v2_yellow_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_yellow_0)).
% 0.14/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.37  fof(c_0_11, plain, ![X13, X14, X15, X16, X17]:(((r2_lattice3(X13,X15,X14)|(X14!=k1_yellow_0(X13,X15)|~r1_yellow_0(X13,X15))|~m1_subset_1(X14,u1_struct_0(X13))|(~v5_orders_2(X13)|~l1_orders_2(X13)))&(~m1_subset_1(X16,u1_struct_0(X13))|(~r2_lattice3(X13,X15,X16)|r1_orders_2(X13,X14,X16))|(X14!=k1_yellow_0(X13,X15)|~r1_yellow_0(X13,X15))|~m1_subset_1(X14,u1_struct_0(X13))|(~v5_orders_2(X13)|~l1_orders_2(X13))))&(((X14=k1_yellow_0(X13,X17)|(m1_subset_1(esk1_3(X13,X14,X17),u1_struct_0(X13))|~r2_lattice3(X13,X17,X14))|~m1_subset_1(X14,u1_struct_0(X13))|(~v5_orders_2(X13)|~l1_orders_2(X13)))&(r1_yellow_0(X13,X17)|(m1_subset_1(esk1_3(X13,X14,X17),u1_struct_0(X13))|~r2_lattice3(X13,X17,X14))|~m1_subset_1(X14,u1_struct_0(X13))|(~v5_orders_2(X13)|~l1_orders_2(X13))))&(((X14=k1_yellow_0(X13,X17)|(r2_lattice3(X13,X17,esk1_3(X13,X14,X17))|~r2_lattice3(X13,X17,X14))|~m1_subset_1(X14,u1_struct_0(X13))|(~v5_orders_2(X13)|~l1_orders_2(X13)))&(r1_yellow_0(X13,X17)|(r2_lattice3(X13,X17,esk1_3(X13,X14,X17))|~r2_lattice3(X13,X17,X14))|~m1_subset_1(X14,u1_struct_0(X13))|(~v5_orders_2(X13)|~l1_orders_2(X13))))&((X14=k1_yellow_0(X13,X17)|(~r1_orders_2(X13,X14,esk1_3(X13,X14,X17))|~r2_lattice3(X13,X17,X14))|~m1_subset_1(X14,u1_struct_0(X13))|(~v5_orders_2(X13)|~l1_orders_2(X13)))&(r1_yellow_0(X13,X17)|(~r1_orders_2(X13,X14,esk1_3(X13,X14,X17))|~r2_lattice3(X13,X17,X14))|~m1_subset_1(X14,u1_struct_0(X13))|(~v5_orders_2(X13)|~l1_orders_2(X13))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.14/0.37  cnf(c_0_12, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  fof(c_0_13, plain, ![X10]:(~l1_orders_2(X10)|k3_yellow_0(X10)=k1_yellow_0(X10,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.14/0.37  fof(c_0_14, plain, ![X11]:(~l1_orders_2(X11)|m1_subset_1(k3_yellow_0(X11),u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.14/0.37  fof(c_0_15, plain, ![X22, X23]:((r2_lattice3(X22,k1_xboole_0,X23)|~m1_subset_1(X23,u1_struct_0(X22))|~l1_orders_2(X22))&(r1_lattice3(X22,k1_xboole_0,X23)|~m1_subset_1(X23,u1_struct_0(X22))|~l1_orders_2(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).
% 0.14/0.37  fof(c_0_16, plain, ![X6, X7, X8]:(~v5_orders_2(X6)|~l1_orders_2(X6)|(~m1_subset_1(X7,u1_struct_0(X6))|(~m1_subset_1(X8,u1_struct_0(X6))|(~r1_orders_2(X6,X7,X8)|~r1_orders_2(X6,X8,X7)|X7=X8)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.14/0.37  cnf(c_0_17, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.37  cnf(c_0_18, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.14/0.37  cnf(c_0_19, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_20, plain, (r2_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.14/0.37  cnf(c_0_21, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk1_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_22, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_23, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.37  cnf(c_0_24, plain, (r1_yellow_0(X1,X2)|~r1_orders_2(X1,X3,esk1_3(X1,X3,X2))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_25, plain, (r1_yellow_0(X1,X2)|m1_subset_1(esk1_3(X1,X3,X2),u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_26, plain, (r1_orders_2(X1,k3_yellow_0(X1),X2)|~r1_yellow_0(X1,k1_xboole_0)|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), ['final']).
% 0.14/0.37  fof(c_0_27, plain, ![X20, X21]:(v2_struct_0(X20)|~v5_orders_2(X20)|~v2_yellow_0(X20)|~l1_orders_2(X20)|(~m1_subset_1(X21,u1_struct_0(X20))|r1_orders_2(X20,X21,k4_yellow_0(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).
% 0.14/0.37  fof(c_0_28, plain, ![X12]:(~l1_orders_2(X12)|m1_subset_1(k4_yellow_0(X12),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).
% 0.14/0.37  fof(c_0_29, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1)))), inference(assume_negation,[status(cth)],[t5_waybel_7])).
% 0.14/0.37  cnf(c_0_30, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|~r2_lattice3(X1,X2,esk1_3(X1,k1_yellow_0(X1,X2),X3))|~r2_lattice3(X1,X3,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_22]), ['final']).
% 0.14/0.37  cnf(c_0_31, plain, (X1=k1_yellow_0(X2,X3)|~r2_lattice3(X2,X3,X1)|~r1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,k1_yellow_0(X2,X3))|~m1_subset_1(k1_yellow_0(X2,X3),u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_23, c_0_17]), ['final']).
% 0.14/0.37  cnf(c_0_32, plain, (r1_yellow_0(X1,X2)|~r2_lattice3(X1,X3,esk1_3(X1,k1_yellow_0(X1,X3),X2))|~r2_lattice3(X1,X2,k1_yellow_0(X1,X3))|~r1_yellow_0(X1,X3)|~m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_25]), ['final']).
% 0.14/0.37  cnf(c_0_33, plain, (k1_yellow_0(X1,X2)=k3_yellow_0(X1)|~r2_lattice3(X1,X2,k3_yellow_0(X1))|~r1_yellow_0(X1,k1_xboole_0)|~m1_subset_1(esk1_3(X1,k3_yellow_0(X1),X2),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_26]), c_0_19])).
% 0.14/0.37  cnf(c_0_34, plain, (r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,k3_yellow_0(X1))|~r1_yellow_0(X1,k1_xboole_0)|~m1_subset_1(esk1_3(X1,k3_yellow_0(X1),X2),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_26]), c_0_19])).
% 0.14/0.37  cnf(c_0_35, plain, (r2_lattice3(X1,X2,X3)|X3!=k1_yellow_0(X1,X2)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_36, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,k4_yellow_0(X1))|~v5_orders_2(X1)|~v2_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.14/0.37  cnf(c_0_37, plain, (m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28]), ['final']).
% 0.14/0.37  fof(c_0_38, plain, ![X19]:((r1_yellow_0(X19,k1_xboole_0)|(v2_struct_0(X19)|~v5_orders_2(X19)|~v1_yellow_0(X19)|~l1_orders_2(X19)))&(r2_yellow_0(X19,u1_struct_0(X19))|(v2_struct_0(X19)|~v5_orders_2(X19)|~v1_yellow_0(X19)|~l1_orders_2(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.14/0.37  fof(c_0_39, plain, ![X9]:((v1_yellow_0(X9)|~v3_yellow_0(X9)|~l1_orders_2(X9))&(v2_yellow_0(X9)|~v3_yellow_0(X9)|~l1_orders_2(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).
% 0.14/0.37  fof(c_0_40, plain, ![X5]:(~l1_orders_2(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.37  fof(c_0_41, negated_conjecture, ((((~v2_struct_0(esk2_0)&v5_orders_2(esk2_0))&v3_yellow_0(esk2_0))&l1_orders_2(esk2_0))&((~v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)!=k3_yellow_0(esk2_0))&(v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)=k3_yellow_0(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).
% 0.14/0.37  cnf(c_0_42, plain, (k1_yellow_0(X1,k1_xboole_0)=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,k1_yellow_0(X1,k1_xboole_0))|~r1_yellow_0(X1,k1_xboole_0)|~m1_subset_1(k1_yellow_0(X1,k1_xboole_0),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_20]), c_0_22]), ['final']).
% 0.14/0.37  cnf(c_0_43, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|~r2_lattice3(X1,X3,k1_yellow_0(X1,X2))|~r2_lattice3(X1,X2,k1_yellow_0(X1,X3))|~r1_yellow_0(X1,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_31, c_0_17]), ['final']).
% 0.14/0.37  cnf(c_0_44, plain, (r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,k1_yellow_0(X1,k1_xboole_0))|~r1_yellow_0(X1,k1_xboole_0)|~m1_subset_1(k1_yellow_0(X1,k1_xboole_0),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_20]), c_0_25]), ['final']).
% 0.14/0.37  cnf(c_0_45, plain, (k1_yellow_0(X1,X2)=k3_yellow_0(X1)|~r2_lattice3(X1,X2,k3_yellow_0(X1))|~r1_yellow_0(X1,k1_xboole_0)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_19]), ['final']).
% 0.14/0.37  cnf(c_0_46, plain, (r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,k3_yellow_0(X1))|~r1_yellow_0(X1,k1_xboole_0)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_19]), ['final']).
% 0.14/0.37  cnf(c_0_47, plain, (X1=k3_yellow_0(X2)|~r1_yellow_0(X2,k1_xboole_0)|~r1_orders_2(X2,X1,k3_yellow_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_26]), c_0_19]), ['final']).
% 0.14/0.37  cnf(c_0_48, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_35]), ['final']).
% 0.14/0.37  cnf(c_0_49, plain, (k4_yellow_0(X1)=X2|v2_struct_0(X1)|~v2_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_36]), c_0_37]), ['final']).
% 0.14/0.37  cnf(c_0_50, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X3,esk1_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_51, plain, (r1_yellow_0(X1,X2)|r2_lattice3(X1,X2,esk1_3(X1,X3,X2))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_52, plain, (r2_yellow_0(X1,u1_struct_0(X1))|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.14/0.37  cnf(c_0_53, plain, (r1_lattice3(X1,k1_xboole_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.14/0.37  cnf(c_0_54, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.14/0.37  cnf(c_0_55, plain, (v2_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.14/0.37  cnf(c_0_56, plain, (v1_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.14/0.37  cnf(c_0_57, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.14/0.37  cnf(c_0_58, negated_conjecture, (v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)=k3_yellow_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.14/0.37  cnf(c_0_59, negated_conjecture, (~v7_struct_0(esk2_0)|k4_yellow_0(esk2_0)!=k3_yellow_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.14/0.37  cnf(c_0_60, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.14/0.37  cnf(c_0_61, negated_conjecture, (v3_yellow_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.14/0.37  cnf(c_0_62, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.14/0.37  cnf(c_0_63, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41]), ['final']).
% 0.14/0.37  # SZS output end Saturation
% 0.14/0.37  # Proof object total steps             : 64
% 0.14/0.37  # Proof object clause steps            : 41
% 0.14/0.37  # Proof object formula steps           : 23
% 0.14/0.37  # Proof object conjectures             : 9
% 0.14/0.37  # Proof object clause conjectures      : 6
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 26
% 0.14/0.37  # Proof object initial formulas used   : 11
% 0.14/0.37  # Proof object generating inferences   : 13
% 0.14/0.37  # Proof object simplifying inferences  : 14
% 0.14/0.37  # Parsed axioms                        : 11
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 26
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 26
% 0.14/0.37  # Processed clauses                    : 53
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 11
% 0.14/0.37  # ...remaining for further processing  : 42
% 0.14/0.37  # Other redundant clauses eliminated   : 2
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 3
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 34
% 0.14/0.37  # ...of the previous two non-trivial   : 29
% 0.14/0.37  # Contextual simplify-reflections      : 13
% 0.14/0.37  # Paramodulations                      : 32
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 2
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 37
% 0.14/0.37  #    Positive orientable unit clauses  : 3
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 33
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 3
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 810
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 45
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 27
% 0.14/0.37  # Unit Clause-clause subsumption calls : 0
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 3528
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.030 s
% 0.14/0.37  # System time              : 0.005 s
% 0.14/0.37  # Total time               : 0.035 s
% 0.14/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
