%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:23 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 153 expanded)
%              Number of clauses        :   32 (  65 expanded)
%              Number of leaves         :    9 (  41 expanded)
%              Depth                    :    5
%              Number of atoms          :  213 ( 612 expanded)
%              Number of equality atoms :   22 (  69 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(d12_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_yellow_0)).

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

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(t44_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

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

fof(t5_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( v7_struct_0(X1)
      <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_waybel_7)).

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

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ~ l1_orders_2(X10)
      | m1_subset_1(k2_yellow_0(X10,X11),u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_10,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | k4_yellow_0(X9) = k2_yellow_0(X9,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7] :
      ( ~ v5_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ r1_orders_2(X5,X6,X7)
      | ~ r1_orders_2(X5,X7,X6)
      | X6 = X7 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

fof(c_0_12,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(k3_yellow_0(X12),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_13,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_14,plain,
    ( k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_15,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_16,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v5_orders_2(X13)
      | ~ v1_yellow_0(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | r1_orders_2(X13,k3_yellow_0(X13),X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v5_orders_2(X15)
      | ~ v2_yellow_0(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | r1_orders_2(X15,X16,k4_yellow_0(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

cnf(c_0_20,plain,
    ( X1 = k3_yellow_0(X2)
    | ~ r1_orders_2(X2,k3_yellow_0(X2),X1)
    | ~ r1_orders_2(X2,X1,k3_yellow_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_yellow_0(X1)
          & l1_orders_2(X1) )
       => ( v7_struct_0(X1)
        <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t5_waybel_7])).

cnf(c_0_24,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,k2_yellow_0(X2,X3),X1)
    | ~ r1_orders_2(X2,X1,k2_yellow_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13]),
    [final]).

cnf(c_0_25,plain,
    ( X1 = k4_yellow_0(X2)
    | ~ r1_orders_2(X2,k4_yellow_0(X2),X1)
    | ~ r1_orders_2(X2,X1,k4_yellow_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_19]),
    [final]).

cnf(c_0_26,plain,
    ( k2_yellow_0(X1,X2) = k3_yellow_0(X1)
    | ~ r1_orders_2(X1,k3_yellow_0(X1),k2_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X2),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13]),
    [final]).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k2_yellow_0(X1,X2))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13]),
    [final]).

cnf(c_0_28,plain,
    ( k4_yellow_0(X1) = k3_yellow_0(X1)
    | ~ r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19]),
    [final]).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19]),
    [final]).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16]),
    [final]).

fof(c_0_31,plain,(
    ! [X8] :
      ( ( v1_yellow_0(X8)
        | ~ v3_yellow_0(X8)
        | ~ l1_orders_2(X8) )
      & ( v2_yellow_0(X8)
        | ~ v3_yellow_0(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).

fof(c_0_32,plain,(
    ! [X4] :
      ( ~ l1_orders_2(X4)
      | l1_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_orders_2(esk1_0)
    & v3_yellow_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ( ~ v7_struct_0(esk1_0)
      | k4_yellow_0(esk1_0) != k3_yellow_0(esk1_0) )
    & ( v7_struct_0(esk1_0)
      | k4_yellow_0(esk1_0) = k3_yellow_0(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

cnf(c_0_34,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X2),k2_yellow_0(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13]),
    [final]).

cnf(c_0_35,plain,
    ( k2_yellow_0(X1,X2) = k4_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k2_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13]),
    [final]).

cnf(c_0_36,plain,
    ( k2_yellow_0(X1,X2) = k3_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v1_yellow_0(X1)
    | ~ r1_orders_2(X1,k2_yellow_0(X1,X2),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27]),
    [final]).

cnf(c_0_37,plain,
    ( k4_yellow_0(X1) = k3_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v1_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29]),
    [final]).

cnf(c_0_38,plain,
    ( k4_yellow_0(X1) = k3_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v2_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30]),
    [final]).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13]),
    [final]).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k4_yellow_0(X1),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19]),
    [final]).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k3_yellow_0(X1))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16]),
    [final]).

cnf(c_0_42,plain,
    ( v2_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_43,plain,
    ( v1_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_44,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( v7_struct_0(esk1_0)
    | k4_yellow_0(esk1_0) = k3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( ~ v7_struct_0(esk1_0)
    | k4_yellow_0(esk1_0) != k3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( v3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.20/0.38  # and selection function SelectNewComplexAHP.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  
% 0.20/0.38  # No proof found!
% 0.20/0.38  # SZS status CounterSatisfiable
% 0.20/0.38  # SZS output start Saturation
% 0.20/0.38  fof(dt_k2_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 0.20/0.38  fof(d12_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k4_yellow_0(X1)=k2_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_yellow_0)).
% 0.20/0.38  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 0.20/0.38  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.20/0.38  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.20/0.38  fof(t45_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,k4_yellow_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_yellow_0)).
% 0.20/0.38  fof(t5_waybel_7, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_waybel_7)).
% 0.20/0.38  fof(cc4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>(v3_yellow_0(X1)=>(v1_yellow_0(X1)&v2_yellow_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_yellow_0)).
% 0.20/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.38  fof(c_0_9, plain, ![X10, X11]:(~l1_orders_2(X10)|m1_subset_1(k2_yellow_0(X10,X11),u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).
% 0.20/0.38  fof(c_0_10, plain, ![X9]:(~l1_orders_2(X9)|k4_yellow_0(X9)=k2_yellow_0(X9,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).
% 0.20/0.38  fof(c_0_11, plain, ![X5, X6, X7]:(~v5_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|(~m1_subset_1(X7,u1_struct_0(X5))|(~r1_orders_2(X5,X6,X7)|~r1_orders_2(X5,X7,X6)|X6=X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.20/0.38  fof(c_0_12, plain, ![X12]:(~l1_orders_2(X12)|m1_subset_1(k3_yellow_0(X12),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.20/0.38  cnf(c_0_13, plain, (m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.38  cnf(c_0_14, plain, (k4_yellow_0(X1)=k2_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.38  cnf(c_0_15, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.20/0.38  cnf(c_0_16, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.20/0.38  fof(c_0_17, plain, ![X13, X14]:(v2_struct_0(X13)|~v5_orders_2(X13)|~v1_yellow_0(X13)|~l1_orders_2(X13)|(~m1_subset_1(X14,u1_struct_0(X13))|r1_orders_2(X13,k3_yellow_0(X13),X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.20/0.38  fof(c_0_18, plain, ![X15, X16]:(v2_struct_0(X15)|~v5_orders_2(X15)|~v2_yellow_0(X15)|~l1_orders_2(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|r1_orders_2(X15,X16,k4_yellow_0(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).
% 0.20/0.38  cnf(c_0_19, plain, (m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.20/0.38  cnf(c_0_20, plain, (X1=k3_yellow_0(X2)|~r1_orders_2(X2,k3_yellow_0(X2),X1)|~r1_orders_2(X2,X1,k3_yellow_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.20/0.38  cnf(c_0_21, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.20/0.38  cnf(c_0_22, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,k4_yellow_0(X1))|~v5_orders_2(X1)|~v2_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.20/0.38  fof(c_0_23, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1)))), inference(assume_negation,[status(cth)],[t5_waybel_7])).
% 0.20/0.38  cnf(c_0_24, plain, (X1=k2_yellow_0(X2,X3)|~r1_orders_2(X2,k2_yellow_0(X2,X3),X1)|~r1_orders_2(X2,X1,k2_yellow_0(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_15, c_0_13]), ['final']).
% 0.20/0.38  cnf(c_0_25, plain, (X1=k4_yellow_0(X2)|~r1_orders_2(X2,k4_yellow_0(X2),X1)|~r1_orders_2(X2,X1,k4_yellow_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_15, c_0_19]), ['final']).
% 0.20/0.38  cnf(c_0_26, plain, (k2_yellow_0(X1,X2)=k3_yellow_0(X1)|~r1_orders_2(X1,k3_yellow_0(X1),k2_yellow_0(X1,X2))|~r1_orders_2(X1,k2_yellow_0(X1,X2),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_20, c_0_13]), ['final']).
% 0.20/0.38  cnf(c_0_27, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k2_yellow_0(X1,X2))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_21, c_0_13]), ['final']).
% 0.20/0.38  cnf(c_0_28, plain, (k4_yellow_0(X1)=k3_yellow_0(X1)|~r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))|~r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_20, c_0_19]), ['final']).
% 0.20/0.38  cnf(c_0_29, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_21, c_0_19]), ['final']).
% 0.20/0.38  cnf(c_0_30, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_22, c_0_16]), ['final']).
% 0.20/0.38  fof(c_0_31, plain, ![X8]:((v1_yellow_0(X8)|~v3_yellow_0(X8)|~l1_orders_2(X8))&(v2_yellow_0(X8)|~v3_yellow_0(X8)|~l1_orders_2(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).
% 0.20/0.38  fof(c_0_32, plain, ![X4]:(~l1_orders_2(X4)|l1_struct_0(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.38  fof(c_0_33, negated_conjecture, ((((~v2_struct_0(esk1_0)&v5_orders_2(esk1_0))&v3_yellow_0(esk1_0))&l1_orders_2(esk1_0))&((~v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)!=k3_yellow_0(esk1_0))&(v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)=k3_yellow_0(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.20/0.38  cnf(c_0_34, plain, (k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)|~r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))|~r1_orders_2(X1,k2_yellow_0(X1,X2),k2_yellow_0(X1,X3))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_24, c_0_13]), ['final']).
% 0.20/0.38  cnf(c_0_35, plain, (k2_yellow_0(X1,X2)=k4_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),k2_yellow_0(X1,X2))|~r1_orders_2(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_25, c_0_13]), ['final']).
% 0.20/0.38  cnf(c_0_36, plain, (k2_yellow_0(X1,X2)=k3_yellow_0(X1)|v2_struct_0(X1)|~v1_yellow_0(X1)|~r1_orders_2(X1,k2_yellow_0(X1,X2),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27]), ['final']).
% 0.20/0.38  cnf(c_0_37, plain, (k4_yellow_0(X1)=k3_yellow_0(X1)|v2_struct_0(X1)|~v1_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29]), ['final']).
% 0.20/0.38  cnf(c_0_38, plain, (k4_yellow_0(X1)=k3_yellow_0(X1)|v2_struct_0(X1)|~v2_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_30]), ['final']).
% 0.20/0.38  cnf(c_0_39, plain, (v2_struct_0(X1)|r1_orders_2(X1,k2_yellow_0(X1,X2),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_22, c_0_13]), ['final']).
% 0.20/0.38  cnf(c_0_40, plain, (v2_struct_0(X1)|r1_orders_2(X1,k4_yellow_0(X1),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_22, c_0_19]), ['final']).
% 0.20/0.38  cnf(c_0_41, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k3_yellow_0(X1))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_21, c_0_16]), ['final']).
% 0.20/0.38  cnf(c_0_42, plain, (v2_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.20/0.38  cnf(c_0_43, plain, (v1_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.20/0.38  cnf(c_0_44, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)=k3_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (~v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)!=k3_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (v3_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.20/0.38  # SZS output end Saturation
% 0.20/0.38  # Proof object total steps             : 51
% 0.20/0.38  # Proof object clause steps            : 32
% 0.20/0.38  # Proof object formula steps           : 19
% 0.20/0.38  # Proof object conjectures             : 9
% 0.20/0.38  # Proof object clause conjectures      : 6
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 15
% 0.20/0.38  # Proof object initial formulas used   : 9
% 0.20/0.38  # Proof object generating inferences   : 17
% 0.20/0.38  # Proof object simplifying inferences  : 0
% 0.20/0.38  # Parsed axioms                        : 9
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 15
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 15
% 0.20/0.38  # Processed clauses                    : 41
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 9
% 0.20/0.38  # ...remaining for further processing  : 32
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 26
% 0.20/0.38  # ...of the previous two non-trivial   : 26
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 26
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
% 0.20/0.38  # Current number of processed clauses  : 32
% 0.20/0.38  #    Positive orientable unit clauses  : 3
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 28
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 0
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 257
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 13
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2014
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.033 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
