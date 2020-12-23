%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:22 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 136 expanded)
%              Number of clauses        :   30 (  56 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :  201 ( 548 expanded)
%              Number of equality atoms :   20 (  59 expanded)
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

fof(dt_k4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_0)).

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

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ~ l1_orders_2(X10)
      | m1_subset_1(k1_yellow_0(X10,X11),u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_10,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | k3_yellow_0(X9) = k1_yellow_0(X9,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

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

cnf(c_0_12,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_15,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v5_orders_2(X13)
      | ~ v1_yellow_0(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | r1_orders_2(X13,k3_yellow_0(X13),X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

fof(c_0_17,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(k4_yellow_0(X12),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).

cnf(c_0_18,plain,
    ( X1 = k3_yellow_0(X2)
    | ~ r1_orders_2(X2,k3_yellow_0(X2),X1)
    | ~ r1_orders_2(X2,X1,k3_yellow_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15]),
    [final]).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_20,plain,
    ( m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v5_orders_2(X15)
      | ~ v2_yellow_0(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | r1_orders_2(X15,X16,k4_yellow_0(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_yellow_0(X1)
          & l1_orders_2(X1) )
       => ( v7_struct_0(X1)
        <=> k4_yellow_0(X1) = k3_yellow_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t5_waybel_7])).

cnf(c_0_23,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,k1_yellow_0(X2,X3),X1)
    | ~ r1_orders_2(X2,X1,k1_yellow_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12]),
    [final]).

cnf(c_0_24,plain,
    ( k1_yellow_0(X1,X2) = k3_yellow_0(X1)
    | ~ r1_orders_2(X1,k3_yellow_0(X1),k1_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_12]),
    [final]).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k1_yellow_0(X1,X2))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12]),
    [final]).

cnf(c_0_26,plain,
    ( X1 = k4_yellow_0(X2)
    | ~ r1_orders_2(X2,k4_yellow_0(X2),X1)
    | ~ r1_orders_2(X2,X1,k4_yellow_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_20]),
    [final]).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

fof(c_0_28,plain,(
    ! [X8] :
      ( ( v1_yellow_0(X8)
        | ~ v3_yellow_0(X8)
        | ~ l1_orders_2(X8) )
      & ( v2_yellow_0(X8)
        | ~ v3_yellow_0(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).

fof(c_0_29,plain,(
    ! [X4] :
      ( ~ l1_orders_2(X4)
      | l1_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_orders_2(esk1_0)
    & v3_yellow_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ( ~ v7_struct_0(esk1_0)
      | k4_yellow_0(esk1_0) != k3_yellow_0(esk1_0) )
    & ( v7_struct_0(esk1_0)
      | k4_yellow_0(esk1_0) = k3_yellow_0(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

cnf(c_0_31,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X3),k1_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_12]),
    [final]).

cnf(c_0_32,plain,
    ( k1_yellow_0(X1,X2) = k3_yellow_0(X1)
    | v2_struct_0(X1)
    | ~ v1_yellow_0(X1)
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k3_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_33,plain,
    ( k1_yellow_0(X1,X2) = k4_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k1_yellow_0(X1,X2))
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_12]),
    [final]).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k1_yellow_0(X1,X2),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_12]),
    [final]).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k3_yellow_0(X1))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_15]),
    [final]).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_15]),
    [final]).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))
    | ~ v1_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k4_yellow_0(X1),k4_yellow_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20]),
    [final]).

cnf(c_0_39,plain,
    ( k3_yellow_0(X1) = k4_yellow_0(X1)
    | ~ r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))
    | ~ r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_15]),
    [final]).

cnf(c_0_40,plain,
    ( v2_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28]),
    [final]).

cnf(c_0_41,plain,
    ( v1_yellow_0(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28]),
    [final]).

cnf(c_0_42,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( v7_struct_0(esk1_0)
    | k4_yellow_0(esk1_0) = k3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( ~ v7_struct_0(esk1_0)
    | k4_yellow_0(esk1_0) != k3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( v3_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:48:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.12/0.37  # and selection function SelectNewComplexAHP.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  
% 0.12/0.37  # No proof found!
% 0.12/0.37  # SZS status CounterSatisfiable
% 0.12/0.37  # SZS output start Saturation
% 0.12/0.37  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.12/0.37  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.12/0.37  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_orders_2)).
% 0.12/0.37  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.12/0.37  fof(dt_k4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_yellow_0)).
% 0.12/0.37  fof(t45_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,k4_yellow_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_0)).
% 0.12/0.37  fof(t5_waybel_7, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_waybel_7)).
% 0.12/0.37  fof(cc4_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>(v3_yellow_0(X1)=>(v1_yellow_0(X1)&v2_yellow_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_0)).
% 0.12/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.12/0.37  fof(c_0_9, plain, ![X10, X11]:(~l1_orders_2(X10)|m1_subset_1(k1_yellow_0(X10,X11),u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.12/0.37  fof(c_0_10, plain, ![X9]:(~l1_orders_2(X9)|k3_yellow_0(X9)=k1_yellow_0(X9,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.12/0.37  fof(c_0_11, plain, ![X5, X6, X7]:(~v5_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|(~m1_subset_1(X7,u1_struct_0(X5))|(~r1_orders_2(X5,X6,X7)|~r1_orders_2(X5,X7,X6)|X6=X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.12/0.37  cnf(c_0_12, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.12/0.37  cnf(c_0_13, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.12/0.37  cnf(c_0_14, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.12/0.37  cnf(c_0_15, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.12/0.37  fof(c_0_16, plain, ![X13, X14]:(v2_struct_0(X13)|~v5_orders_2(X13)|~v1_yellow_0(X13)|~l1_orders_2(X13)|(~m1_subset_1(X14,u1_struct_0(X13))|r1_orders_2(X13,k3_yellow_0(X13),X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.12/0.37  fof(c_0_17, plain, ![X12]:(~l1_orders_2(X12)|m1_subset_1(k4_yellow_0(X12),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_yellow_0])])).
% 0.12/0.37  cnf(c_0_18, plain, (X1=k3_yellow_0(X2)|~r1_orders_2(X2,k3_yellow_0(X2),X1)|~r1_orders_2(X2,X1,k3_yellow_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_14, c_0_15]), ['final']).
% 0.12/0.37  cnf(c_0_19, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_20, plain, (m1_subset_1(k4_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.12/0.37  fof(c_0_21, plain, ![X15, X16]:(v2_struct_0(X15)|~v5_orders_2(X15)|~v2_yellow_0(X15)|~l1_orders_2(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|r1_orders_2(X15,X16,k4_yellow_0(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_yellow_0])])])])).
% 0.12/0.37  fof(c_0_22, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_yellow_0(X1))&l1_orders_2(X1))=>(v7_struct_0(X1)<=>k4_yellow_0(X1)=k3_yellow_0(X1)))), inference(assume_negation,[status(cth)],[t5_waybel_7])).
% 0.12/0.37  cnf(c_0_23, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,k1_yellow_0(X2,X3),X1)|~r1_orders_2(X2,X1,k1_yellow_0(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_14, c_0_12]), ['final']).
% 0.12/0.37  cnf(c_0_24, plain, (k1_yellow_0(X1,X2)=k3_yellow_0(X1)|~r1_orders_2(X1,k3_yellow_0(X1),k1_yellow_0(X1,X2))|~r1_orders_2(X1,k1_yellow_0(X1,X2),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_12]), ['final']).
% 0.12/0.37  cnf(c_0_25, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k1_yellow_0(X1,X2))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_19, c_0_12]), ['final']).
% 0.12/0.37  cnf(c_0_26, plain, (X1=k4_yellow_0(X2)|~r1_orders_2(X2,k4_yellow_0(X2),X1)|~r1_orders_2(X2,X1,k4_yellow_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_14, c_0_20]), ['final']).
% 0.12/0.37  cnf(c_0_27, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,k4_yellow_0(X1))|~v5_orders_2(X1)|~v2_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.12/0.37  fof(c_0_28, plain, ![X8]:((v1_yellow_0(X8)|~v3_yellow_0(X8)|~l1_orders_2(X8))&(v2_yellow_0(X8)|~v3_yellow_0(X8)|~l1_orders_2(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_yellow_0])])])).
% 0.12/0.37  fof(c_0_29, plain, ![X4]:(~l1_orders_2(X4)|l1_struct_0(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.12/0.37  fof(c_0_30, negated_conjecture, ((((~v2_struct_0(esk1_0)&v5_orders_2(esk1_0))&v3_yellow_0(esk1_0))&l1_orders_2(esk1_0))&((~v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)!=k3_yellow_0(esk1_0))&(v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)=k3_yellow_0(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.12/0.37  cnf(c_0_31, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|~r1_orders_2(X1,k1_yellow_0(X1,X3),k1_yellow_0(X1,X2))|~r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_23, c_0_12]), ['final']).
% 0.12/0.37  cnf(c_0_32, plain, (k1_yellow_0(X1,X2)=k3_yellow_0(X1)|v2_struct_0(X1)|~v1_yellow_0(X1)|~r1_orders_2(X1,k1_yellow_0(X1,X2),k3_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.12/0.37  cnf(c_0_33, plain, (k1_yellow_0(X1,X2)=k4_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),k1_yellow_0(X1,X2))|~r1_orders_2(X1,k1_yellow_0(X1,X2),k4_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_12]), ['final']).
% 0.12/0.37  cnf(c_0_34, plain, (v2_struct_0(X1)|r1_orders_2(X1,k1_yellow_0(X1,X2),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_27, c_0_12]), ['final']).
% 0.12/0.37  cnf(c_0_35, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k3_yellow_0(X1))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_19, c_0_15]), ['final']).
% 0.12/0.37  cnf(c_0_36, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_27, c_0_15]), ['final']).
% 0.12/0.37  cnf(c_0_37, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))|~v1_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.12/0.37  cnf(c_0_38, plain, (v2_struct_0(X1)|r1_orders_2(X1,k4_yellow_0(X1),k4_yellow_0(X1))|~v2_yellow_0(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_27, c_0_20]), ['final']).
% 0.12/0.37  cnf(c_0_39, plain, (k3_yellow_0(X1)=k4_yellow_0(X1)|~r1_orders_2(X1,k4_yellow_0(X1),k3_yellow_0(X1))|~r1_orders_2(X1,k3_yellow_0(X1),k4_yellow_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_15]), ['final']).
% 0.12/0.37  cnf(c_0_40, plain, (v2_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28]), ['final']).
% 0.12/0.37  cnf(c_0_41, plain, (v1_yellow_0(X1)|~v3_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28]), ['final']).
% 0.12/0.37  cnf(c_0_42, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)=k3_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (~v7_struct_0(esk1_0)|k4_yellow_0(esk1_0)!=k3_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (v3_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.12/0.37  # SZS output end Saturation
% 0.12/0.37  # Proof object total steps             : 49
% 0.12/0.37  # Proof object clause steps            : 30
% 0.12/0.37  # Proof object formula steps           : 19
% 0.12/0.37  # Proof object conjectures             : 9
% 0.12/0.37  # Proof object clause conjectures      : 6
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 9
% 0.12/0.37  # Proof object generating inferences   : 15
% 0.12/0.37  # Proof object simplifying inferences  : 0
% 0.12/0.37  # Parsed axioms                        : 9
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 15
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 15
% 0.12/0.37  # Processed clauses                    : 38
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 8
% 0.12/0.37  # ...remaining for further processing  : 30
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 23
% 0.12/0.37  # ...of the previous two non-trivial   : 23
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 23
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 30
% 0.12/0.37  #    Positive orientable unit clauses  : 3
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 26
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 0
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 223
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 12
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 8
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1935
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.032 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
