%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_9__t33_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:09 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 (3378 expanded)
%              Number of clauses        :   52 (1023 expanded)
%              Number of leaves         :    7 ( 830 expanded)
%              Depth                    :   16
%              Number of atoms          :  403 (41236 expanded)
%              Number of equality atoms :    6 (2091 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   32 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t33_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t46_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',dt_m2_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t30_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t31_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t32_waybel_9)).

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

fof(c_0_8,plain,(
    ! [X49,X50,X51,X53] :
      ( ( m2_yellow_6(esk12_3(X49,X50,X51),X49,X50)
        | r2_hidden(X51,k10_yellow_6(X49,X50))
        | ~ m1_subset_1(X51,u1_struct_0(X49))
        | v2_struct_0(X50)
        | ~ v4_orders_2(X50)
        | ~ v7_waybel_0(X50)
        | ~ l1_waybel_0(X50,X49)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( ~ m2_yellow_6(X53,X49,esk12_3(X49,X50,X51))
        | ~ r2_hidden(X51,k10_yellow_6(X49,X53))
        | r2_hidden(X51,k10_yellow_6(X49,X50))
        | ~ m1_subset_1(X51,u1_struct_0(X49))
        | v2_struct_0(X50)
        | ~ v4_orders_2(X50)
        | ~ v7_waybel_0(X50)
        | ~ l1_waybel_0(X50,X49)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_yellow_6])])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X8,X9] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & v8_pre_topc(esk1_0)
      & v1_compts_1(esk1_0)
      & l1_pre_topc(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & v4_orders_2(esk2_0)
      & v7_waybel_0(esk2_0)
      & l1_waybel_0(esk2_0,esk1_0)
      & ( ~ m1_subset_1(X8,u1_struct_0(esk1_0))
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ r3_waybel_9(esk1_0,esk2_0,X8)
        | ~ r3_waybel_9(esk1_0,esk2_0,X9)
        | X8 = X9 )
      & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
      & r3_waybel_9(esk1_0,esk2_0,esk3_0)
      & ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_10,plain,
    ( m2_yellow_6(esk12_3(X1,X2,X3),X1,X2)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v2_struct_0(X21)
        | ~ m2_yellow_6(X21,X19,X20)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19) )
      & ( v4_orders_2(X21)
        | ~ m2_yellow_6(X21,X19,X20)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19) )
      & ( v7_waybel_0(X21)
        | ~ m2_yellow_6(X21,X19,X20)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19) )
      & ( l1_waybel_0(X21,X19)
        | ~ m2_yellow_6(X21,X19,X20)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_16,negated_conjecture,
    ( m2_yellow_6(esk12_3(esk1_0,X1,esk3_0),esk1_0,X1)
    | r2_hidden(esk3_0,k10_yellow_6(esk1_0,X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m2_yellow_6(esk12_3(esk1_0,esk2_0,esk3_0),esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

fof(c_0_24,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_25,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X36,X37] :
      ( ( m1_subset_1(esk10_2(X36,X37),u1_struct_0(X36))
        | v2_struct_0(X37)
        | ~ v4_orders_2(X37)
        | ~ v7_waybel_0(X37)
        | ~ l1_waybel_0(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ v8_pre_topc(X36)
        | ~ v1_compts_1(X36)
        | ~ l1_pre_topc(X36) )
      & ( r3_waybel_9(X36,X37,esk10_2(X36,X37))
        | v2_struct_0(X37)
        | ~ v4_orders_2(X37)
        | ~ v7_waybel_0(X37)
        | ~ l1_waybel_0(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ v8_pre_topc(X36)
        | ~ v1_compts_1(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).

cnf(c_0_29,negated_conjecture,
    ( l1_waybel_0(esk12_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_17]),c_0_18]),c_0_19])]),c_0_14]),c_0_21])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v7_waybel_0(esk12_3(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_17]),c_0_18]),c_0_19])]),c_0_14]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v4_orders_2(esk12_3(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_17]),c_0_18]),c_0_19])]),c_0_14]),c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ v2_struct_0(esk12_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_17]),c_0_18]),c_0_19])]),c_0_14]),c_0_21])).

fof(c_0_34,plain,(
    ! [X39,X40,X41,X42] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | v2_struct_0(X40)
      | ~ v4_orders_2(X40)
      | ~ v7_waybel_0(X40)
      | ~ l1_waybel_0(X40,X39)
      | ~ m2_yellow_6(X41,X39,X40)
      | ~ m1_subset_1(X42,u1_struct_0(X39))
      | ~ r3_waybel_9(X39,X41,X42)
      | r3_waybel_9(X39,X40,X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk10_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( l1_waybel_0(esk12_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_12])])).

cnf(c_0_37,negated_conjecture,
    ( v7_waybel_0(esk12_3(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_12])])).

cnf(c_0_38,negated_conjecture,
    ( v4_orders_2(esk12_3(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_12])])).

cnf(c_0_39,negated_conjecture,
    ( v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( v8_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk12_3(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_12])])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk10_2(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_12]),c_0_39]),c_0_40]),c_0_13])]),c_0_14]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r3_waybel_9(esk1_0,X1,esk10_2(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0)))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(X2,esk1_0,X1)
    | ~ r3_waybel_9(esk1_0,X2,esk10_2(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0)))
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_45,plain,
    ( r3_waybel_9(X1,X2,esk10_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_46,plain,(
    ! [X43,X44,X45] :
      ( ( m2_yellow_6(esk11_3(X43,X44,X45),X43,X44)
        | ~ r3_waybel_9(X43,X44,X45)
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( r2_hidden(X45,k10_yellow_6(X43,esk11_3(X43,X44,X45)))
        | ~ r3_waybel_9(X43,X44,X45)
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( X1 = X2
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ r3_waybel_9(esk1_0,esk2_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk2_0,esk10_2(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0)))
    | ~ m2_yellow_6(X1,esk1_0,esk2_0)
    | ~ r3_waybel_9(esk1_0,X1,esk10_2(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_17]),c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0),esk10_2(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_36]),c_0_37]),c_0_38]),c_0_12]),c_0_39]),c_0_40]),c_0_13])]),c_0_14]),c_0_41])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk11_3(X2,X3,X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( X1 = esk3_0
    | ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_11])])).

cnf(c_0_53,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk2_0,esk10_2(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_50])])).

cnf(c_0_54,plain,
    ( r2_hidden(X4,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m2_yellow_6(X1,X2,esk12_3(X2,X3,X4))
    | ~ r2_hidden(X4,k10_yellow_6(X2,X1))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk11_3(esk1_0,X1,esk3_0)))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_56,negated_conjecture,
    ( esk10_2(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_43])])).

cnf(c_0_57,plain,
    ( m2_yellow_6(esk11_3(X1,X2,X3),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,X1))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(X2,esk1_0,esk12_3(esk1_0,X1,esk3_0))
    | ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,X2))
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk11_3(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0),esk3_0)))
    | ~ r3_waybel_9(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_36]),c_0_37]),c_0_38])]),c_0_41])).

cnf(c_0_60,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( m2_yellow_6(esk11_3(esk1_0,X1,esk3_0),esk1_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk1_0,esk12_3(esk1_0,esk2_0,esk3_0))
    | ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk11_3(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_64,negated_conjecture,
    ( m2_yellow_6(esk11_3(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0),esk3_0),esk1_0,esk12_3(esk1_0,esk2_0,esk3_0))
    | ~ r3_waybel_9(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_36]),c_0_37]),c_0_38])]),c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( ~ m2_yellow_6(esk11_3(esk1_0,esk12_3(esk1_0,esk2_0,esk3_0),esk3_0),esk1_0,esk12_3(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_60])]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
