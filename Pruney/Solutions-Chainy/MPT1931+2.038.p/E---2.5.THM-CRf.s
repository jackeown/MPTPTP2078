%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:16 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 220 expanded)
%              Number of clauses        :   35 (  80 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  202 (1097 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   35 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ~ r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t29_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_o_2_2_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(o_2_2_yellow_6(X1,X2),u1_struct_0(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_12,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_waybel_0(X27,X28,X29)
        | ~ r2_waybel_0(X27,X28,k6_subset_1(u1_struct_0(X27),X29))
        | v2_struct_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27) )
      & ( r2_waybel_0(X27,X28,k6_subset_1(u1_struct_0(X27),X29))
        | r1_waybel_0(X27,X28,X29)
        | v2_struct_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).

fof(c_0_13,plain,(
    ! [X15,X16] : k6_subset_1(X15,X16) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t29_yellow_6])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( v1_xboole_0(X10)
      | ~ r1_tarski(X10,X9)
      | ~ r1_xboole_0(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_16,plain,(
    ! [X7,X8] : r1_tarski(k4_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_17,plain,
    ( r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v4_orders_2(esk4_0)
    & v7_waybel_0(esk4_0)
    & l1_waybel_0(esk4_0,esk3_0)
    & ~ r1_waybel_0(esk3_0,esk4_0,u1_struct_0(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | X13 = X14
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X11,X12] : r1_xboole_0(k4_xboole_0(X11,X12),X12) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_24,plain,(
    ! [X19,X20,X21,X22,X24,X26] :
      ( ( m1_subset_1(esk1_4(X19,X20,X21,X22),u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ r2_waybel_0(X19,X20,X21)
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( r1_orders_2(X20,X22,esk1_4(X19,X20,X21,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ r2_waybel_0(X19,X20,X21)
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( r2_hidden(k2_waybel_0(X19,X20,esk1_4(X19,X20,X21,X22)),X21)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ r2_waybel_0(X19,X20,X21)
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( m1_subset_1(esk2_3(X19,X20,X24),u1_struct_0(X20))
        | r2_waybel_0(X19,X20,X24)
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X20))
        | ~ r1_orders_2(X20,esk2_3(X19,X20,X24),X26)
        | ~ r2_hidden(k2_waybel_0(X19,X20,X26),X24)
        | r2_waybel_0(X19,X20,X24)
        | v2_struct_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_waybel_0(X1,X2,X3)
    | r2_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_32,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | v2_struct_0(X31)
      | ~ v4_orders_2(X31)
      | ~ v7_waybel_0(X31)
      | ~ l1_waybel_0(X31,X30)
      | m1_subset_1(o_2_2_yellow_6(X30,X31),u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_2_yellow_6])])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_waybel_0(esk3_0,esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk4_0,X1)
    | r2_waybel_0(esk3_0,esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_40,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ r1_tarski(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_41,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_42,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk4_0))
    | r2_waybel_0(esk3_0,esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_27])]),c_0_28]),c_0_29])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(o_2_2_yellow_6(X1,X2),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v7_waybel_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( r2_waybel_0(esk3_0,esk4_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk1_4(esk3_0,esk4_0,X1,X2),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_26]),c_0_27])]),c_0_28]),c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(o_2_2_yellow_6(esk3_0,esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_26]),c_0_45]),c_0_46]),c_0_27])]),c_0_28]),c_0_29])).

cnf(c_0_53,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk1_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( r2_waybel_0(esk3_0,esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk1_4(esk3_0,esk4_0,X1,o_2_2_yellow_6(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_26]),c_0_27])]),c_0_28]),c_0_29]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_56,c_0_57]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:59:56 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.33  # Version: 2.5pre002
% 0.18/0.33  # No SInE strategy applied
% 0.18/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.18/0.36  # and selection function SelectCQArNTNpEqFirst.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.028 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t9_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>~(r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_waybel_0)).
% 0.18/0.36  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.18/0.36  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.18/0.36  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.18/0.36  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.18/0.36  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.18/0.36  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.18/0.36  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.18/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.36  fof(dt_o_2_2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(o_2_2_yellow_6(X1,X2),u1_struct_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_2_yellow_6)).
% 0.18/0.36  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.18/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.36  fof(c_0_12, plain, ![X27, X28, X29]:((~r1_waybel_0(X27,X28,X29)|~r2_waybel_0(X27,X28,k6_subset_1(u1_struct_0(X27),X29))|(v2_struct_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~l1_struct_0(X27)))&(r2_waybel_0(X27,X28,k6_subset_1(u1_struct_0(X27),X29))|r1_waybel_0(X27,X28,X29)|(v2_struct_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~l1_struct_0(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).
% 0.18/0.36  fof(c_0_13, plain, ![X15, X16]:k6_subset_1(X15,X16)=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.18/0.36  fof(c_0_14, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.18/0.36  fof(c_0_15, plain, ![X9, X10]:(v1_xboole_0(X10)|(~r1_tarski(X10,X9)|~r1_xboole_0(X10,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.18/0.36  fof(c_0_16, plain, ![X7, X8]:r1_tarski(k4_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.18/0.36  cnf(c_0_17, plain, (r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_18, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  fof(c_0_19, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&((((~v2_struct_0(esk4_0)&v4_orders_2(esk4_0))&v7_waybel_0(esk4_0))&l1_waybel_0(esk4_0,esk3_0))&~r1_waybel_0(esk3_0,esk4_0,u1_struct_0(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.18/0.36  fof(c_0_20, plain, ![X13, X14]:(~v1_xboole_0(X13)|X13=X14|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.18/0.36  cnf(c_0_21, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  fof(c_0_23, plain, ![X11, X12]:r1_xboole_0(k4_xboole_0(X11,X12),X12), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.18/0.36  fof(c_0_24, plain, ![X19, X20, X21, X22, X24, X26]:((((m1_subset_1(esk1_4(X19,X20,X21,X22),u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))|~r2_waybel_0(X19,X20,X21)|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(r1_orders_2(X20,X22,esk1_4(X19,X20,X21,X22))|~m1_subset_1(X22,u1_struct_0(X20))|~r2_waybel_0(X19,X20,X21)|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&(r2_hidden(k2_waybel_0(X19,X20,esk1_4(X19,X20,X21,X22)),X21)|~m1_subset_1(X22,u1_struct_0(X20))|~r2_waybel_0(X19,X20,X21)|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))&((m1_subset_1(esk2_3(X19,X20,X24),u1_struct_0(X20))|r2_waybel_0(X19,X20,X24)|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19)))&(~m1_subset_1(X26,u1_struct_0(X20))|~r1_orders_2(X20,esk2_3(X19,X20,X24),X26)|~r2_hidden(k2_waybel_0(X19,X20,X26),X24)|r2_waybel_0(X19,X20,X24)|(v2_struct_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~l1_struct_0(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.18/0.36  cnf(c_0_25, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r1_waybel_0(X1,X2,X3)|r2_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.36  cnf(c_0_26, negated_conjecture, (l1_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_27, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_30, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.36  cnf(c_0_31, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.36  cnf(c_0_32, plain, (v1_xboole_0(k4_xboole_0(X1,X2))|~r1_xboole_0(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.36  cnf(c_0_33, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.36  cnf(c_0_34, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.36  fof(c_0_35, plain, ![X30, X31]:(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30)|m1_subset_1(o_2_2_yellow_6(X30,X31),u1_struct_0(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_2_yellow_6])])])).
% 0.18/0.36  cnf(c_0_36, negated_conjecture, (~r1_waybel_0(esk3_0,esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_37, negated_conjecture, (r1_waybel_0(esk3_0,esk4_0,X1)|r2_waybel_0(esk3_0,esk4_0,k4_xboole_0(u1_struct_0(esk3_0),X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), c_0_28]), c_0_29])).
% 0.18/0.36  cnf(c_0_38, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.36  cnf(c_0_39, plain, (v1_xboole_0(k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.18/0.36  fof(c_0_40, plain, ![X17, X18]:(~r2_hidden(X17,X18)|~r1_tarski(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.18/0.36  fof(c_0_41, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.36  cnf(c_0_42, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.36  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk4_0))|r2_waybel_0(esk3_0,esk4_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_26]), c_0_27])]), c_0_28]), c_0_29])).
% 0.18/0.36  cnf(c_0_44, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(o_2_2_yellow_6(X1,X2),u1_struct_0(X2))|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.36  cnf(c_0_45, negated_conjecture, (v7_waybel_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_46, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_47, negated_conjecture, (r2_waybel_0(esk3_0,esk4_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.36  cnf(c_0_48, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.36  cnf(c_0_49, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.36  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.36  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk1_4(esk3_0,esk4_0,X1,X2),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_26]), c_0_27])]), c_0_28]), c_0_29])).
% 0.18/0.36  cnf(c_0_52, negated_conjecture, (m1_subset_1(o_2_2_yellow_6(esk3_0,esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_26]), c_0_45]), c_0_46]), c_0_27])]), c_0_28]), c_0_29])).
% 0.18/0.36  cnf(c_0_53, plain, (r2_hidden(k2_waybel_0(X1,X2,esk1_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.36  cnf(c_0_54, negated_conjecture, (r2_waybel_0(esk3_0,esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.36  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.18/0.36  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk1_4(esk3_0,esk4_0,X1,o_2_2_yellow_6(esk3_0,esk4_0)),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.36  cnf(c_0_57, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_26]), c_0_27])]), c_0_28]), c_0_29]), c_0_55])).
% 0.18/0.36  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_56, c_0_57]), c_0_57]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 59
% 0.18/0.36  # Proof object clause steps            : 35
% 0.18/0.36  # Proof object formula steps           : 24
% 0.18/0.36  # Proof object conjectures             : 19
% 0.18/0.36  # Proof object clause conjectures      : 16
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 20
% 0.18/0.36  # Proof object initial formulas used   : 12
% 0.18/0.36  # Proof object generating inferences   : 12
% 0.18/0.36  # Proof object simplifying inferences  : 29
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 12
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 23
% 0.18/0.36  # Removed in clause preprocessing      : 1
% 0.18/0.36  # Initial clauses in saturation        : 22
% 0.18/0.36  # Processed clauses                    : 74
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 2
% 0.18/0.36  # ...remaining for further processing  : 72
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 2
% 0.18/0.36  # Generated clauses                    : 75
% 0.18/0.36  # ...of the previous two non-trivial   : 63
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 65
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 38
% 0.18/0.36  #    Positive orientable unit clauses  : 13
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 6
% 0.18/0.36  #    Non-unit-clauses                  : 19
% 0.18/0.36  # Current number of unprocessed clauses: 30
% 0.18/0.36  # ...number of literals in the above   : 65
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 35
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 248
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 37
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.18/0.36  # Unit Clause-clause subsumption calls : 24
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 26
% 0.18/0.36  # BW rewrite match successes           : 2
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 3828
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.036 s
% 0.18/0.36  # System time              : 0.000 s
% 0.18/0.36  # Total time               : 0.036 s
% 0.18/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
