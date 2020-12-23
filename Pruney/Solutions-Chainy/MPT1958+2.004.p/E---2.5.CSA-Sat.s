%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:22 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 240 expanded)
%              Number of clauses        :   42 ( 106 expanded)
%              Number of leaves         :   10 (  64 expanded)
%              Depth                    :    6
%              Number of atoms          :  263 ( 908 expanded)
%              Number of equality atoms :   31 ( 111 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

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

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(d12_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).

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

fof(t45_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_0)).

fof(t5_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( v7_struct_0(X1)
      <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_waybel_7)).

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

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ~ l1_orders_2(X11)
      | m1_subset_1(k1_yellow_0(X11,X12),u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_11,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | k3_yellow_0(X9) = k1_yellow_0(X9,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7] :
      ( ~ v5_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ r1_orders_2(X5,X6,X7)
      | ~ r1_orders_2(X5,X7,X6)
      | X6 = X7 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ~ l1_orders_2(X13)
      | m1_subset_1(k2_yellow_0(X13,X14),u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_16,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | k4_yellow_0(X10) = k2_yellow_0(X10,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).

cnf(c_0_17,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_18,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v5_orders_2(X15)
      | ~ v1_yellow_0(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | r1_orders_2(X15,k3_yellow_0(X15),X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_21,plain,
    ( k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

fof(c_0_22,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v5_orders_2(X17)
      | ~ v2_yellow_0(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | r1_orders_2(X17,X18,k4_yellow_0(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).

cnf(c_0_23,plain,
    ( X1 = k3_yellow_0(X2)
    | ~ r1_orders_2(X2,k3_yellow_0(X2),X1)
    | ~ r1_orders_2(X2,X1,k3_yellow_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_25,plain,
    ( m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

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
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,k1_yellow_0(X2,X3),X1)
    | ~ r1_orders_2(X2,X1,k1_yellow_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13]),
    [final]).

cnf(c_0_29,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,k2_yellow_0(X2,X3),X1)
    | ~ r1_orders_2(X2,X1,k2_yellow_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_20]),
    [final]).

cnf(c_0_30,plain,
    ( k1_yellow_0(X1,X2) = k3_yellow_0(X1)
    | ~ r1_orders_2(X1,k3_yellow_0(X1),k1_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_13]),
    [final]).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k1_yellow_0(X1,X2))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13]),
    [final]).

cnf(c_0_32,plain,
    ( k2_yellow_0(X1,X2) = k3_yellow_0(X1)
    | ~ r1_orders_2(X1,k3_yellow_0(X1),k2_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X2),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20]),
    [final]).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k2_yellow_0(X1,X2))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20]),
    [final]).

cnf(c_0_34,plain,
    ( X1 = k4_yellow_0(X2)
    | ~ r1_orders_2(X2,k4_yellow_0(X2),X1)
    | ~ r1_orders_2(X2,X1,k4_yellow_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_25]),
    [final]).

cnf(c_0_35,plain,
    ( k3_yellow_0(X1) = k4_yellow_0(X1)
    | ~ r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25]),
    [final]).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18]),
    [final]).

fof(c_0_38,plain,(
    ! [X8] :
      ( ( v1_yellow_0(X8)
        | ~ v3_yellow_0(X8)
        | ~ l1_orders_2(X8) )
      & ( v2_yellow_0(X8)
        | ~ v3_yellow_0(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).

fof(c_0_39,plain,(
    ! [X4] :
      ( ~ l1_orders_2(X4)
      | l1_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_orders_2(esk1_0)
    & v3_yellow_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ( ~ v7_struct_0(esk1_0)
      | k4_yellow_0(esk1_0) != k3_yellow_0(esk1_0) )
    & ( v7_struct_0(esk1_0)
      | k4_yellow_0(esk1_0) = k3_yellow_0(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).

cnf(c_0_41,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X3),k1_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_13]),
    [final]).

cnf(c_0_42,plain,
    ( k1_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X3),k1_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k2_yellow_0(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_13]),
    [final]).

cnf(c_0_43,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X2),k2_yellow_0(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20]),
    [final]).

cnf(c_0_44,plain,
    ( k1_yellow_0(X1,X2) = k3_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v1_yellow_0(X1)
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31]),
    [final]).

cnf(c_0_45,plain,
    ( k2_yellow_0(X1,X2) = k3_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v1_yellow_0(X1)
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X2),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33]),
    [final]).

cnf(c_0_46,plain,
    ( k1_yellow_0(X1,X2) = k4_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k1_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_13]),
    [final]).

cnf(c_0_47,plain,
    ( k2_yellow_0(X1,X2) = k4_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k2_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20]),
    [final]).

cnf(c_0_48,plain,
    ( k3_yellow_0(X1) = k4_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v1_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_49,plain,
    ( k3_yellow_0(X1) = k4_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v2_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37]),
    [final]).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k1_yellow_0(X1,X2),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_13]),
    [final]).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20]),
    [final]).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k4_yellow_0(X1),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25]),
    [final]).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k3_yellow_0(X1))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18]),
    [final]).

cnf(c_0_54,plain,
    ( v2_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_55,plain,
    ( v1_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_56,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( v7_struct_0(esk1_0)
    | k4_yellow_0(esk1_0) = k3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( ~ v7_struct_0(esk1_0)
    | k4_yellow_0(esk1_0) != k3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( v3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.19/0.37  # and selection function SelectNewComplexAHP.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  
% 0.19/0.37  # No proof found!
% 0.19/0.37  # SZS status CounterSatisfiable
% 0.19/0.37  # SZS output start Saturation
% 0.19/0.37  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.19/0.37  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.19/0.37  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_orders_2)).
% 0.19/0.37  fof(dt_k2_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 0.19/0.37  fof(d12_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k4_yellow_0(X1)=k2_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_yellow_0)).
% 0.19/0.37  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.19/0.37  fof(t45_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,k4_yellow_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_0)).
% 0.19/0.37  fof(t5_waybel_7, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_waybel_7)).
% 0.19/0.37  fof(cc4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>(v3_yellow_0(X1)=>(v1_yellow_0(X1)&v2_yellow_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_0)).
% 0.19/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.37  fof(c_0_10, plain, ![X11, X12]:(~l1_orders_2(X11)|m1_subset_1(k1_yellow_0(X11,X12),u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.19/0.37  fof(c_0_11, plain, ![X9]:(~l1_orders_2(X9)|k3_yellow_0(X9)=k1_yellow_0(X9,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.19/0.37  fof(c_0_12, plain, ![X5, X6, X7]:(~v5_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|(~m1_subset_1(X7,u1_struct_0(X5))|(~r1_orders_2(X5,X6,X7)|~r1_orders_2(X5,X7,X6)|X6=X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.19/0.37  cnf(c_0_13, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.19/0.37  cnf(c_0_14, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.19/0.37  fof(c_0_15, plain, ![X13, X14]:(~l1_orders_2(X13)|m1_subset_1(k2_yellow_0(X13,X14),u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).
% 0.19/0.37  fof(c_0_16, plain, ![X10]:(~l1_orders_2(X10)|k4_yellow_0(X10)=k2_yellow_0(X10,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).
% 0.19/0.37  cnf(c_0_17, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.19/0.37  cnf(c_0_18, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.19/0.37  fof(c_0_19, plain, ![X15, X16]:(v2_struct_0(X15)|~v5_orders_2(X15)|~v1_yellow_0(X15)|~l1_orders_2(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|r1_orders_2(X15,k3_yellow_0(X15),X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.19/0.37  cnf(c_0_20, plain, (m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.19/0.37  cnf(c_0_21, plain, (k4_yellow_0(X1)=k2_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.19/0.37  fof(c_0_22, plain, ![X17, X18]:(v2_struct_0(X17)|~v5_orders_2(X17)|~v2_yellow_0(X17)|~l1_orders_2(X17)|(~m1_subset_1(X18,u1_struct_0(X17))|r1_orders_2(X17,X18,k4_yellow_0(X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).
% 0.19/0.37  cnf(c_0_23, plain, (X1=k3_yellow_0(X2)|~r1_orders_2(X2,k3_yellow_0(X2),X1)|~r1_orders_2(X2,X1,k3_yellow_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.19/0.37  cnf(c_0_24, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.19/0.37  cnf(c_0_25, plain, (m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 0.19/0.37  cnf(c_0_26, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,k4_yellow_0(X1))|~v5_orders_2(X1)|~v2_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.19/0.37  fof(c_0_27, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1)))), inference(assume_negation,[status(cth)],[t5_waybel_7])).
% 0.19/0.37  cnf(c_0_28, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,k1_yellow_0(X2,X3),X1)|~r1_orders_2(X2,X1,k1_yellow_0(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_17, c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_29, plain, (X1=k2_yellow_0(X2,X3)|~r1_orders_2(X2,k2_yellow_0(X2,X3),X1)|~r1_orders_2(X2,X1,k2_yellow_0(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_17, c_0_20]), ['final']).
% 0.19/0.37  cnf(c_0_30, plain, (k1_yellow_0(X1,X2)=k3_yellow_0(X1)|~r1_orders_2(X1,k3_yellow_0(X1),k1_yellow_0(X1,X2))|~r1_orders_2(X1,k1_yellow_0(X1,X2),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_23, c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_31, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k1_yellow_0(X1,X2))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_24, c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_32, plain, (k2_yellow_0(X1,X2)=k3_yellow_0(X1)|~r1_orders_2(X1,k3_yellow_0(X1),k2_yellow_0(X1,X2))|~r1_orders_2(X1,k2_yellow_0(X1,X2),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_23, c_0_20]), ['final']).
% 0.19/0.37  cnf(c_0_33, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k2_yellow_0(X1,X2))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_24, c_0_20]), ['final']).
% 0.19/0.37  cnf(c_0_34, plain, (X1=k4_yellow_0(X2)|~r1_orders_2(X2,k4_yellow_0(X2),X1)|~r1_orders_2(X2,X1,k4_yellow_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_17, c_0_25]), ['final']).
% 0.19/0.37  cnf(c_0_35, plain, (k3_yellow_0(X1)=k4_yellow_0(X1)|~r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))|~r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_23, c_0_25]), ['final']).
% 0.19/0.37  cnf(c_0_36, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.19/0.37  cnf(c_0_37, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_18]), ['final']).
% 0.19/0.37  fof(c_0_38, plain, ![X8]:((v1_yellow_0(X8)|~v3_yellow_0(X8)|~l1_orders_2(X8))&(v2_yellow_0(X8)|~v3_yellow_0(X8)|~l1_orders_2(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).
% 0.19/0.37  fof(c_0_39, plain, ![X4]:(~l1_orders_2(X4)|l1_struct_0(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.37  fof(c_0_40, negated_conjecture, ((((~v2_struct_0(esk1_0)&v5_orders_2(esk1_0))&v3_yellow_0(esk1_0))&l1_orders_2(esk1_0))&((~v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)!=k3_yellow_0(esk1_0))&(v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)=k3_yellow_0(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).
% 0.19/0.37  cnf(c_0_41, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|~r1_orders_2(X1,k1_yellow_0(X1,X3),k1_yellow_0(X1,X2))|~r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_42, plain, (k1_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|~r1_orders_2(X1,k2_yellow_0(X1,X3),k1_yellow_0(X1,X2))|~r1_orders_2(X1,k1_yellow_0(X1,X2),k2_yellow_0(X1,X3))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_29, c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_43, plain, (k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|~r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))|~r1_orders_2(X1,k2_yellow_0(X1,X2),k2_yellow_0(X1,X3))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_29, c_0_20]), ['final']).
% 0.19/0.37  cnf(c_0_44, plain, (k1_yellow_0(X1,X2)=k3_yellow_0(X1)|v2_struct_0(X1)|~v1_yellow_0(X1)|~r1_orders_2(X1,k1_yellow_0(X1,X2),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31]), ['final']).
% 0.19/0.37  cnf(c_0_45, plain, (k2_yellow_0(X1,X2)=k3_yellow_0(X1)|v2_struct_0(X1)|~v1_yellow_0(X1)|~r1_orders_2(X1,k2_yellow_0(X1,X2),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33]), ['final']).
% 0.19/0.37  cnf(c_0_46, plain, (k1_yellow_0(X1,X2)=k4_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),k1_yellow_0(X1,X2))|~r1_orders_2(X1,k1_yellow_0(X1,X2),k4_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_47, plain, (k2_yellow_0(X1,X2)=k4_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),k2_yellow_0(X1,X2))|~r1_orders_2(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_20]), ['final']).
% 0.19/0.37  cnf(c_0_48, plain, (k3_yellow_0(X1)=k4_yellow_0(X1)|v2_struct_0(X1)|~v1_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.19/0.37  cnf(c_0_49, plain, (k3_yellow_0(X1)=k4_yellow_0(X1)|v2_struct_0(X1)|~v2_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_35, c_0_37]), ['final']).
% 0.19/0.37  cnf(c_0_50, plain, (v2_struct_0(X1)|r1_orders_2(X1,k1_yellow_0(X1,X2),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_51, plain, (v2_struct_0(X1)|r1_orders_2(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_20]), ['final']).
% 0.19/0.37  cnf(c_0_52, plain, (v2_struct_0(X1)|r1_orders_2(X1,k4_yellow_0(X1),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_25]), ['final']).
% 0.19/0.37  cnf(c_0_53, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k3_yellow_0(X1))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_24, c_0_18]), ['final']).
% 0.19/0.37  cnf(c_0_54, plain, (v2_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.19/0.37  cnf(c_0_55, plain, (v1_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.19/0.37  cnf(c_0_56, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)=k3_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (~v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)!=k3_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (v3_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.19/0.37  # SZS output end Saturation
% 0.19/0.37  # Proof object total steps             : 63
% 0.19/0.37  # Proof object clause steps            : 42
% 0.19/0.37  # Proof object formula steps           : 21
% 0.19/0.37  # Proof object conjectures             : 9
% 0.19/0.37  # Proof object clause conjectures      : 6
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 16
% 0.19/0.37  # Proof object initial formulas used   : 10
% 0.19/0.37  # Proof object generating inferences   : 26
% 0.19/0.37  # Proof object simplifying inferences  : 0
% 0.19/0.37  # Parsed axioms                        : 10
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 61
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 19
% 0.19/0.37  # ...remaining for further processing  : 42
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 45
% 0.19/0.37  # ...of the previous two non-trivial   : 45
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 45
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 42
% 0.19/0.37  #    Positive orientable unit clauses  : 3
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 38
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 0
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 479
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 25
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 19
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2580
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.027 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.034 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
