%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_6)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).

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
    ! [X10,X11] :
      ( ( m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ v8_pre_topc(X10)
        | ~ v1_compts_1(X10)
        | ~ l1_pre_topc(X10) )
      & ( r3_waybel_9(X10,X11,esk1_2(X10,X11))
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ v8_pre_topc(X10)
        | ~ v1_compts_1(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16] :
      ( v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(X14)
      | ~ v4_orders_2(X14)
      | ~ v7_waybel_0(X14)
      | ~ l1_waybel_0(X14,X13)
      | ~ m2_yellow_6(X15,X13,X14)
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | ~ r3_waybel_9(X13,X15,X16)
      | r3_waybel_9(X13,X14,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

fof(c_0_11,plain,(
    ! [X21,X22,X23,X25] :
      ( ( m2_yellow_6(esk3_3(X21,X22,X23),X21,X22)
        | r2_hidden(X23,k10_yellow_6(X21,X22))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ m2_yellow_6(X25,X21,esk3_3(X21,X22,X23))
        | ~ r2_hidden(X23,k10_yellow_6(X21,X25))
        | r2_hidden(X23,k10_yellow_6(X21,X22))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
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
    ( r3_waybel_9(X1,X2,esk1_2(X1,X2))
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
    ( m2_yellow_6(esk3_3(X1,X2,X3),X1,X2)
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
    ( X1 = esk1_2(esk4_0,esk5_0)
    | ~ r3_waybel_9(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
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
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | r3_waybel_9(X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r3_waybel_9(X2,esk3_3(X2,X3,X1),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v4_orders_2(esk3_3(X2,X3,X1))
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
    | v7_waybel_0(esk3_3(X2,X3,X1))
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
    | l1_waybel_0(esk3_3(X2,X3,X1),X2)
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
    | ~ v2_struct_0(esk3_3(X2,X3,X1))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_28])).

fof(c_0_39,plain,(
    ! [X17,X18,X19] :
      ( ( m2_yellow_6(esk2_3(X17,X18,X19),X17,X18)
        | ~ r3_waybel_9(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X18)
        | ~ v4_orders_2(X18)
        | ~ v7_waybel_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(X19,k10_yellow_6(X17,esk2_3(X17,X18,X19)))
        | ~ r3_waybel_9(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X18)
        | ~ v4_orders_2(X18)
        | ~ v7_waybel_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk1_2(esk4_0,esk5_0)
    | ~ r3_waybel_9(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | r3_waybel_9(X2,X3,esk1_2(X2,esk3_3(X2,X3,X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(esk1_2(X2,esk3_3(X2,X3,X1)),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v1_compts_1(X2)
    | ~ v8_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_15]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(X4,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m2_yellow_6(X1,X2,esk3_3(X2,X3,X4))
    | ~ r2_hidden(X4,k10_yellow_6(X2,X1))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,plain,
    ( m2_yellow_6(esk2_3(X1,X2,X3),X1,X2)
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
    ( esk1_2(esk4_0,esk3_3(esk4_0,esk5_0,X1)) = esk1_2(esk4_0,esk5_0)
    | r2_hidden(X1,k10_yellow_6(esk4_0,esk5_0))
    | ~ m1_subset_1(esk1_2(esk4_0,esk3_3(esk4_0,esk5_0,X1)),u1_struct_0(esk4_0))
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
    | ~ r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,esk3_3(X2,X3,X1),X4)))
    | ~ r3_waybel_9(X2,esk3_3(X2,X3,X1),X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,X3,X1)))
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
    ( esk1_2(esk4_0,esk3_3(esk4_0,esk5_0,X1)) = esk1_2(esk4_0,esk5_0)
    | r2_hidden(X1,k10_yellow_6(esk4_0,esk5_0))
    | v2_struct_0(esk3_3(esk4_0,esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l1_waybel_0(esk3_3(esk4_0,esk5_0,X1),esk4_0)
    | ~ v7_waybel_0(esk3_3(esk4_0,esk5_0,X1))
    | ~ v4_orders_2(esk3_3(esk4_0,esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_33]),c_0_16]),c_0_17]),c_0_18]),c_0_22])]),c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( esk6_0 = esk1_2(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_45]),c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k10_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,esk3_3(X2,X3,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk4_0,esk5_0))
    | r3_waybel_9(esk4_0,esk3_3(esk4_0,esk5_0,X1),esk1_2(esk4_0,esk5_0))
    | v2_struct_0(esk3_3(esk4_0,esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l1_waybel_0(esk3_3(esk4_0,esk5_0,X1),esk4_0)
    | ~ v7_waybel_0(esk3_3(esk4_0,esk5_0,X1))
    | ~ v4_orders_2(esk3_3(esk4_0,esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_49]),c_0_16]),c_0_17]),c_0_18]),c_0_22])]),c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk4_0,esk5_0),k10_yellow_6(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | ~ l1_waybel_0(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)),esk4_0)
    | ~ v7_waybel_0(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | ~ v4_orders_2(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_23]),c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | ~ v7_waybel_0(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | ~ v4_orders_2(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_37]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_24]),c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0)))
    | ~ v4_orders_2(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_36]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_24]),c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( v2_struct_0(esk3_3(esk4_0,esk5_0,esk1_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_35]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_24]),c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_59]),c_0_54]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_55]),c_0_24]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------
