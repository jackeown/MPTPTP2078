%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:46 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   61 (1476 expanded)
%              Number of clauses        :   46 ( 441 expanded)
%              Number of leaves         :    7 ( 371 expanded)
%              Depth                    :   13
%              Number of atoms          :  464 (18440 expanded)
%              Number of equality atoms :    9 ( 924 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v1_compts_1(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r3_waybel_9(X1,X2,X3)
                        & r3_waybel_9(X1,X2,X4) )
                     => X3 = X4 ) ) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r3_waybel_9(X1,X2,X3)
                 => r2_hidden(X3,k10_yellow_6(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_9)).

fof(t30_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v1_compts_1(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r3_waybel_9(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_waybel_9)).

fof(t31_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m2_yellow_6(X3,X1,X2)
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r3_waybel_9(X1,X3,X4)
                   => r3_waybel_9(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

fof(t46_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( ~ r2_hidden(X3,k10_yellow_6(X1,X2))
                  & ! [X4] :
                      ( m2_yellow_6(X4,X1,X2)
                     => ? [X5] :
                          ( m2_yellow_6(X5,X1,X4)
                          & r2_hidden(X3,k10_yellow_6(X1,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_yellow_6)).

fof(dt_m2_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m2_yellow_6(X3,X1,X2)
         => ( ~ v2_struct_0(X3)
            & v4_orders_2(X3)
            & v7_waybel_0(X3)
            & l1_waybel_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t32_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( r3_waybel_9(X1,X2,X3)
                  & ! [X4] :
                      ( m2_yellow_6(X4,X1,X2)
                     => ~ r2_hidden(X3,k10_yellow_6(X1,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v8_pre_topc(X1)
          & v1_compts_1(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( ( r3_waybel_9(X1,X2,X3)
                          & r3_waybel_9(X1,X2,X4) )
                       => X3 = X4 ) ) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( r3_waybel_9(X1,X2,X3)
                   => r2_hidden(X3,k10_yellow_6(X1,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_waybel_9])).

fof(c_0_8,negated_conjecture,(
    ! [X28,X29] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & v8_pre_topc(esk4_0)
      & v1_compts_1(esk4_0)
      & l1_pre_topc(esk4_0)
      & ~ v2_struct_0(esk5_0)
      & v4_orders_2(esk5_0)
      & v7_waybel_0(esk5_0)
      & l1_waybel_0(esk5_0,esk4_0)
      & ( ~ m1_subset_1(X28,u1_struct_0(esk4_0))
        | ~ m1_subset_1(X29,u1_struct_0(esk4_0))
        | ~ r3_waybel_9(esk4_0,esk5_0,X28)
        | ~ r3_waybel_9(esk4_0,esk5_0,X29)
        | X28 = X29 )
      & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
      & r3_waybel_9(esk4_0,esk5_0,esk6_0)
      & ~ r2_hidden(esk6_0,k10_yellow_6(esk4_0,esk5_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

fof(c_0_9,plain,(
    ! [X15,X16] :
      ( ( m1_subset_1(esk2_2(X15,X16),u1_struct_0(X15))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ v8_pre_topc(X15)
        | ~ v1_compts_1(X15)
        | ~ l1_pre_topc(X15) )
      & ( r3_waybel_9(X15,X16,esk2_2(X15,X16))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ v8_pre_topc(X15)
        | ~ v1_compts_1(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).

fof(c_0_10,plain,(
    ! [X18,X19,X20,X21] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(X19)
      | ~ v4_orders_2(X19)
      | ~ v7_waybel_0(X19)
      | ~ l1_waybel_0(X19,X18)
      | ~ m2_yellow_6(X20,X18,X19)
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | ~ r3_waybel_9(X18,X20,X21)
      | r3_waybel_9(X18,X19,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X14] :
      ( ( m2_yellow_6(esk1_3(X10,X11,X12),X10,X11)
        | r2_hidden(X12,k10_yellow_6(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ m2_yellow_6(X14,X10,esk1_3(X10,X11,X12))
        | ~ r2_hidden(X12,k10_yellow_6(X10,X14))
        | r2_hidden(X12,k10_yellow_6(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_yellow_6])])])])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v2_struct_0(X9)
        | ~ m2_yellow_6(X9,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,X7) )
      & ( v4_orders_2(X9)
        | ~ m2_yellow_6(X9,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,X7) )
      & ( v7_waybel_0(X9)
        | ~ m2_yellow_6(X9,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,X7) )
      & ( l1_waybel_0(X9,X7)
        | ~ m2_yellow_6(X9,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_struct_0(X7)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

fof(c_0_13,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_14,negated_conjecture,
    ( X1 = X2
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ r3_waybel_9(esk4_0,esk5_0,X1)
    | ~ r3_waybel_9(esk4_0,esk5_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r3_waybel_9(X1,X2,esk2_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_compts_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( v8_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v7_waybel_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r3_waybel_9(X1,X2,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( m2_yellow_6(esk1_3(X1,X2,X3),X1,X2)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( X1 = esk2_2(esk4_0,esk5_0)
    | ~ r3_waybel_9(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(esk2_2(esk4_0,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,plain,
    ( r3_waybel_9(X1,X2,X3)
    | r2_hidden(X4,k10_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,esk1_3(X1,X2,X4),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v4_orders_2(esk1_3(X2,X3,X1))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_26]),c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v7_waybel_0(esk1_3(X2,X3,X1))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | l1_waybel_0(esk1_3(X2,X3,X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v2_struct_0(esk1_3(X2,X3,X1))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_28])).

fof(c_0_39,plain,(
    ! [X22,X23,X24] :
      ( ( m2_yellow_6(esk3_3(X22,X23,X24),X22,X23)
        | ~ r3_waybel_9(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(X24,k10_yellow_6(X22,esk3_3(X22,X23,X24)))
        | ~ r3_waybel_9(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk2_2(esk4_0,esk5_0)
    | ~ r3_waybel_9(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_41,plain,
    ( r3_waybel_9(X1,X2,esk2_2(X1,esk1_3(X1,X2,X3)))
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_compts_1(X1)
    | ~ v8_pre_topc(X1)
    | ~ m1_subset_1(esk2_2(X1,esk1_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_15]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(X4,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m2_yellow_6(X1,X2,esk1_3(X2,X3,X4))
    | ~ r2_hidden(X4,k10_yellow_6(X2,X1))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,plain,
    ( m2_yellow_6(esk3_3(X1,X2,X3),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk2_2(esk4_0,esk1_3(esk4_0,esk5_0,X1)) = esk2_2(esk4_0,esk5_0)
    | r2_hidden(X1,k10_yellow_6(esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_2(esk4_0,esk1_3(esk4_0,esk5_0,X1)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( r3_waybel_9(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r3_waybel_9(X2,esk1_3(X2,X3,X1),X4)
    | ~ r2_hidden(X1,k10_yellow_6(X2,esk3_3(X2,esk1_3(X2,X3,X1),X4)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk3_3(X2,X3,X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( esk2_2(esk4_0,esk1_3(esk4_0,esk5_0,X1)) = esk2_2(esk4_0,esk5_0)
    | r2_hidden(X1,k10_yellow_6(esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk4_0,esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l1_waybel_0(esk1_3(esk4_0,esk5_0,X1),esk4_0)
    | ~ v7_waybel_0(esk1_3(esk4_0,esk5_0,X1))
    | ~ v4_orders_2(esk1_3(esk4_0,esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_33]),c_0_16]),c_0_17]),c_0_18]),c_0_22])]),c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( esk6_0 = esk2_2(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_45]),c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k10_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,esk1_3(X2,X3,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( r3_waybel_9(esk4_0,esk1_3(esk4_0,esk5_0,X1),esk2_2(esk4_0,esk5_0))
    | r2_hidden(X1,k10_yellow_6(esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk4_0,esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l1_waybel_0(esk1_3(esk4_0,esk5_0,X1),esk4_0)
    | ~ v7_waybel_0(esk1_3(esk4_0,esk5_0,X1))
    | ~ v4_orders_2(esk1_3(esk4_0,esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_49]),c_0_16]),c_0_17]),c_0_18]),c_0_22])]),c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk4_0,esk5_0),k10_yellow_6(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))
    | ~ l1_waybel_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)),esk4_0)
    | ~ v7_waybel_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))
    | ~ v4_orders_2(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_23]),c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))
    | ~ v7_waybel_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))
    | ~ v4_orders_2(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_37]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_24]),c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))
    | ~ v4_orders_2(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_36]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_24]),c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( v2_struct_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_35]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_24]),c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_59]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_24]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:01:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t33_waybel_9, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r3_waybel_9(X1,X2,X3)&r3_waybel_9(X1,X2,X4))=>X3=X4)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)=>r2_hidden(X3,k10_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_waybel_9)).
% 0.14/0.38  fof(t30_waybel_9, axiom, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_waybel_9)).
% 0.14/0.38  fof(t31_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 0.14/0.38  fof(t46_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((~(r2_hidden(X3,k10_yellow_6(X1,X2)))&![X4]:(m2_yellow_6(X4,X1,X2)=>?[X5]:(m2_yellow_6(X5,X1,X4)&r2_hidden(X3,k10_yellow_6(X1,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_yellow_6)).
% 0.14/0.38  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.14/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.38  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r3_waybel_9(X1,X2,X3)&r3_waybel_9(X1,X2,X4))=>X3=X4)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)=>r2_hidden(X3,k10_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t33_waybel_9])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ![X28, X29]:(((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v8_pre_topc(esk4_0))&v1_compts_1(esk4_0))&l1_pre_topc(esk4_0))&((((~v2_struct_0(esk5_0)&v4_orders_2(esk5_0))&v7_waybel_0(esk5_0))&l1_waybel_0(esk5_0,esk4_0))&((~m1_subset_1(X28,u1_struct_0(esk4_0))|(~m1_subset_1(X29,u1_struct_0(esk4_0))|(~r3_waybel_9(esk4_0,esk5_0,X28)|~r3_waybel_9(esk4_0,esk5_0,X29)|X28=X29)))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(r3_waybel_9(esk4_0,esk5_0,esk6_0)&~r2_hidden(esk6_0,k10_yellow_6(esk4_0,esk5_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X15, X16]:((m1_subset_1(esk2_2(X15,X16),u1_struct_0(X15))|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~v8_pre_topc(X15)|~v1_compts_1(X15)|~l1_pre_topc(X15)))&(r3_waybel_9(X15,X16,esk2_2(X15,X16))|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~v8_pre_topc(X15)|~v1_compts_1(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X18, X19, X20, X21]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(v2_struct_0(X19)|~v4_orders_2(X19)|~v7_waybel_0(X19)|~l1_waybel_0(X19,X18)|(~m2_yellow_6(X20,X18,X19)|(~m1_subset_1(X21,u1_struct_0(X18))|(~r3_waybel_9(X18,X20,X21)|r3_waybel_9(X18,X19,X21)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X10, X11, X12, X14]:((m2_yellow_6(esk1_3(X10,X11,X12),X10,X11)|r2_hidden(X12,k10_yellow_6(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|(v2_struct_0(X11)|~v4_orders_2(X11)|~v7_waybel_0(X11)|~l1_waybel_0(X11,X10))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~m2_yellow_6(X14,X10,esk1_3(X10,X11,X12))|~r2_hidden(X12,k10_yellow_6(X10,X14))|r2_hidden(X12,k10_yellow_6(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|(v2_struct_0(X11)|~v4_orders_2(X11)|~v7_waybel_0(X11)|~l1_waybel_0(X11,X10))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_yellow_6])])])])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X7, X8, X9]:((((~v2_struct_0(X9)|~m2_yellow_6(X9,X7,X8)|(v2_struct_0(X7)|~l1_struct_0(X7)|v2_struct_0(X8)|~v4_orders_2(X8)|~v7_waybel_0(X8)|~l1_waybel_0(X8,X7)))&(v4_orders_2(X9)|~m2_yellow_6(X9,X7,X8)|(v2_struct_0(X7)|~l1_struct_0(X7)|v2_struct_0(X8)|~v4_orders_2(X8)|~v7_waybel_0(X8)|~l1_waybel_0(X8,X7))))&(v7_waybel_0(X9)|~m2_yellow_6(X9,X7,X8)|(v2_struct_0(X7)|~l1_struct_0(X7)|v2_struct_0(X8)|~v4_orders_2(X8)|~v7_waybel_0(X8)|~l1_waybel_0(X8,X7))))&(l1_waybel_0(X9,X7)|~m2_yellow_6(X9,X7,X8)|(v2_struct_0(X7)|~l1_struct_0(X7)|v2_struct_0(X8)|~v4_orders_2(X8)|~v7_waybel_0(X8)|~l1_waybel_0(X8,X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X6]:(~l1_pre_topc(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (X1=X2|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~r3_waybel_9(esk4_0,esk5_0,X1)|~r3_waybel_9(esk4_0,esk5_0,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_15, plain, (r3_waybel_9(X1,X2,esk2_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (v1_compts_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (v8_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (l1_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (v7_waybel_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_25, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~r3_waybel_9(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_26, plain, (m2_yellow_6(esk1_3(X1,X2,X3),X1,X2)|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_27, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_28, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_29, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_30, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_31, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (X1=esk2_2(esk4_0,esk5_0)|~r3_waybel_9(esk4_0,esk5_0,X1)|~m1_subset_1(esk2_2(esk4_0,esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.14/0.38  cnf(c_0_33, plain, (m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_34, plain, (r3_waybel_9(X1,X2,X3)|r2_hidden(X4,k10_yellow_6(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,esk1_3(X1,X2,X4),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  cnf(c_0_35, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|v4_orders_2(esk1_3(X2,X3,X1))|v2_struct_0(X2)|v2_struct_0(X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_26]), c_0_28])).
% 0.14/0.38  cnf(c_0_36, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|v7_waybel_0(esk1_3(X2,X3,X1))|v2_struct_0(X2)|v2_struct_0(X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_26]), c_0_28])).
% 0.14/0.38  cnf(c_0_37, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|l1_waybel_0(esk1_3(X2,X3,X1),X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_28])).
% 0.14/0.38  cnf(c_0_38, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|v2_struct_0(X2)|v2_struct_0(X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~v2_struct_0(esk1_3(X2,X3,X1))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_28])).
% 0.14/0.38  fof(c_0_39, plain, ![X22, X23, X24]:((m2_yellow_6(esk3_3(X22,X23,X24),X22,X23)|~r3_waybel_9(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|(v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(r2_hidden(X24,k10_yellow_6(X22,esk3_3(X22,X23,X24)))|~r3_waybel_9(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|(v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (X1=esk2_2(esk4_0,esk5_0)|~r3_waybel_9(esk4_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.14/0.38  cnf(c_0_41, plain, (r3_waybel_9(X1,X2,esk2_2(X1,esk1_3(X1,X2,X3)))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v1_compts_1(X1)|~v8_pre_topc(X1)|~m1_subset_1(esk2_2(X1,esk1_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_15]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.14/0.38  cnf(c_0_42, plain, (r2_hidden(X4,k10_yellow_6(X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|~m2_yellow_6(X1,X2,esk1_3(X2,X3,X4))|~r2_hidden(X4,k10_yellow_6(X2,X1))|~m1_subset_1(X4,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_43, plain, (m2_yellow_6(esk3_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (esk2_2(esk4_0,esk1_3(esk4_0,esk5_0,X1))=esk2_2(esk4_0,esk5_0)|r2_hidden(X1,k10_yellow_6(esk4_0,esk5_0))|~m1_subset_1(esk2_2(esk4_0,esk1_3(esk4_0,esk5_0,X1)),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r3_waybel_9(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_47, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|v2_struct_0(X2)|v2_struct_0(X3)|~r3_waybel_9(X2,esk1_3(X2,X3,X1),X4)|~r2_hidden(X1,k10_yellow_6(X2,esk3_3(X2,esk1_3(X2,X3,X1),X4)))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.14/0.38  cnf(c_0_48, plain, (r2_hidden(X1,k10_yellow_6(X2,esk3_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (esk2_2(esk4_0,esk1_3(esk4_0,esk5_0,X1))=esk2_2(esk4_0,esk5_0)|r2_hidden(X1,k10_yellow_6(esk4_0,esk5_0))|v2_struct_0(esk1_3(esk4_0,esk5_0,X1))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l1_waybel_0(esk1_3(esk4_0,esk5_0,X1),esk4_0)|~v7_waybel_0(esk1_3(esk4_0,esk5_0,X1))|~v4_orders_2(esk1_3(esk4_0,esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_33]), c_0_16]), c_0_17]), c_0_18]), c_0_22])]), c_0_24])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (esk6_0=esk2_2(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_45]), c_0_46])])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk6_0,k10_yellow_6(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_52, plain, (r2_hidden(X1,k10_yellow_6(X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,esk1_3(X2,X3,X1),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (r3_waybel_9(esk4_0,esk1_3(esk4_0,esk5_0,X1),esk2_2(esk4_0,esk5_0))|r2_hidden(X1,k10_yellow_6(esk4_0,esk5_0))|v2_struct_0(esk1_3(esk4_0,esk5_0,X1))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l1_waybel_0(esk1_3(esk4_0,esk5_0,X1),esk4_0)|~v7_waybel_0(esk1_3(esk4_0,esk5_0,X1))|~v4_orders_2(esk1_3(esk4_0,esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_49]), c_0_16]), c_0_17]), c_0_18]), c_0_22])]), c_0_24])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk2_2(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_46, c_0_50])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (~r2_hidden(esk2_2(esk4_0,esk5_0),k10_yellow_6(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_51, c_0_50])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (v2_struct_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))|~l1_waybel_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)),esk4_0)|~v7_waybel_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))|~v4_orders_2(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_55]), c_0_23]), c_0_24])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (v2_struct_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))|~v7_waybel_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))|~v4_orders_2(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_37]), c_0_54]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_55]), c_0_24]), c_0_23])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (v2_struct_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))|~v4_orders_2(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_36]), c_0_54]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_55]), c_0_24]), c_0_23])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (v2_struct_0(esk1_3(esk4_0,esk5_0,esk2_2(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_35]), c_0_54]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_55]), c_0_24]), c_0_23])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_59]), c_0_54]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_55]), c_0_24]), c_0_23]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 61
% 0.14/0.38  # Proof object clause steps            : 46
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 29
% 0.14/0.38  # Proof object clause conjectures      : 26
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 25
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 19
% 0.14/0.38  # Proof object simplifying inferences  : 112
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 7
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 25
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 25
% 0.14/0.39  # Processed clauses                    : 98
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 6
% 0.14/0.39  # ...remaining for further processing  : 92
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 6
% 0.14/0.39  # Backward-rewritten                   : 5
% 0.14/0.39  # Generated clauses                    : 79
% 0.14/0.39  # ...of the previous two non-trivial   : 75
% 0.14/0.39  # Contextual simplify-reflections      : 28
% 0.14/0.39  # Paramodulations                      : 79
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 56
% 0.14/0.39  #    Positive orientable unit clauses  : 12
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 3
% 0.14/0.39  #    Non-unit-clauses                  : 41
% 0.14/0.39  # Current number of unprocessed clauses: 25
% 0.14/0.39  # ...number of literals in the above   : 383
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 36
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1589
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 99
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 39
% 0.14/0.39  # Unit Clause-clause subsumption calls : 42
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 5
% 0.14/0.39  # BW rewrite match successes           : 2
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 8565
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.041 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.044 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
