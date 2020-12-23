%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:19 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 561 expanded)
%              Number of clauses        :   45 ( 179 expanded)
%              Number of leaves         :    9 ( 140 expanded)
%              Depth                    :   12
%              Number of atoms          :  445 (4099 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   81 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_yellow_6,conjecture,(
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
             => r1_tarski(k10_yellow_6(X1,X2),k10_yellow_6(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(t27_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m2_yellow_6(X3,X1,X2)
             => ! [X4] :
                  ( r2_waybel_0(X1,X3,X4)
                 => r2_waybel_0(X1,X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).

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

fof(d18_yellow_6,axiom,(
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
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k10_yellow_6(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_connsp_2(X5,X1,X4)
                         => r1_waybel_0(X1,X2,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k10_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
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
               => r1_tarski(k10_yellow_6(X1,X2),k10_yellow_6(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_yellow_6])).

fof(c_0_10,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v4_orders_2(esk6_0)
    & v7_waybel_0(esk6_0)
    & l1_waybel_0(esk6_0,esk5_0)
    & m2_yellow_6(esk7_0,esk5_0,esk6_0)
    & ~ r1_tarski(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v2_struct_0(X32)
        | ~ m2_yellow_6(X32,X30,X31)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30) )
      & ( v4_orders_2(X32)
        | ~ m2_yellow_6(X32,X30,X31)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30) )
      & ( v7_waybel_0(X32)
        | ~ m2_yellow_6(X32,X30,X31)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30) )
      & ( l1_waybel_0(X32,X30)
        | ~ m2_yellow_6(X32,X30,X31)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_13,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X33,X34,X35,X36] :
      ( v2_struct_0(X33)
      | ~ l1_struct_0(X33)
      | v2_struct_0(X34)
      | ~ v4_orders_2(X34)
      | ~ v7_waybel_0(X34)
      | ~ l1_waybel_0(X34,X33)
      | ~ m2_yellow_6(X35,X33,X34)
      | ~ r2_waybel_0(X33,X35,X36)
      | r2_waybel_0(X33,X34,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r1_waybel_0(X16,X17,X18)
        | ~ r2_waybel_0(X16,X17,k6_subset_1(u1_struct_0(X16),X18))
        | v2_struct_0(X17)
        | ~ l1_waybel_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16) )
      & ( r2_waybel_0(X16,X17,k6_subset_1(u1_struct_0(X16),X18))
        | r1_waybel_0(X16,X17,X18)
        | v2_struct_0(X17)
        | ~ l1_waybel_0(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).

cnf(c_0_17,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m2_yellow_6(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v7_waybel_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_25,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_23]),c_0_24])])).

fof(c_0_30,plain,(
    ! [X19,X20,X21,X22,X23,X27] :
      ( ( ~ r2_hidden(X22,X21)
        | ~ m1_connsp_2(X23,X19,X22)
        | r1_waybel_0(X19,X20,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | X21 != k10_yellow_6(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_connsp_2(esk2_4(X19,X20,X21,X22),X19,X22)
        | r2_hidden(X22,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | X21 != k10_yellow_6(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r1_waybel_0(X19,X20,esk2_4(X19,X20,X21,X22))
        | r2_hidden(X22,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | X21 != k10_yellow_6(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_3(X19,X20,X21),u1_struct_0(X19))
        | X21 = k10_yellow_6(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_connsp_2(esk4_3(X19,X20,X21),X19,esk3_3(X19,X20,X21))
        | ~ r2_hidden(esk3_3(X19,X20,X21),X21)
        | X21 = k10_yellow_6(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r1_waybel_0(X19,X20,esk4_3(X19,X20,X21))
        | ~ r2_hidden(esk3_3(X19,X20,X21),X21)
        | X21 = k10_yellow_6(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_3(X19,X20,X21),X21)
        | ~ m1_connsp_2(X27,X19,esk3_3(X19,X20,X21))
        | r1_waybel_0(X19,X20,X27)
        | X21 = k10_yellow_6(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_31,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | m1_subset_1(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_32,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ v4_orders_2(X29)
      | ~ v7_waybel_0(X29)
      | ~ l1_waybel_0(X29,X28)
      | m1_subset_1(k10_yellow_6(X28,X29),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,X1)
    | ~ r2_waybel_0(esk5_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_34,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk7_0,k6_subset_1(u1_struct_0(esk5_0),X1))
    | r1_waybel_0(esk5_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24])]),c_0_29]),c_0_23])).

cnf(c_0_35,plain,
    ( r1_waybel_0(X4,X5,X3)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_connsp_2(X3,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | X2 != k10_yellow_6(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v4_orders_2(X5)
    | ~ v7_waybel_0(X5)
    | ~ l1_waybel_0(X5,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_39,plain,
    ( r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,k6_subset_1(u1_struct_0(esk5_0),X1))
    | r1_waybel_0(esk5_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X4)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X4,k10_yellow_6(X1,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_35,c_0_36])]),c_0_37])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_connsp_2(esk2_4(X1,X2,X3,X4),X1,X4)
    | r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(X3,k10_yellow_6(X2,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_pre_topc(X2)
    | ~ r1_waybel_0(X2,X1,esk2_4(X2,X1,k10_yellow_6(X2,X1),X3))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk7_0,X1)
    | ~ r1_waybel_0(esk5_0,esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_21]),c_0_24])]),c_0_22]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( v7_waybel_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_50,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(X1,X2),X4)
    | ~ m1_connsp_2(X3,X1,esk1_2(k10_yellow_6(X1,X2),X4))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( m1_connsp_2(esk2_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk5_0,esk7_0))
    | ~ r1_waybel_0(esk5_0,esk6_0,esk2_4(esk5_0,esk7_0,k10_yellow_6(esk5_0,esk7_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_28]),c_0_14])]),c_0_23]),c_0_29])).

cnf(c_0_55,plain,
    ( r1_waybel_0(X1,X2,esk2_4(X1,X3,k10_yellow_6(X1,X3),esk1_2(k10_yellow_6(X1,X2),X4)))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(esk1_2(k10_yellow_6(X1,X2),X4),k10_yellow_6(X1,X3))
    | r1_tarski(k10_yellow_6(X1,X2),X4)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk1_2(k10_yellow_6(X1,X2),X4),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k10_yellow_6(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_51]),c_0_14])]),c_0_23])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_2(k10_yellow_6(esk5_0,esk6_0),X1),k10_yellow_6(esk5_0,esk7_0))
    | r1_tarski(k10_yellow_6(esk5_0,esk6_0),X1)
    | ~ m1_subset_1(esk1_2(k10_yellow_6(esk5_0,esk6_0),X1),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_19]),c_0_49]),c_0_20]),c_0_50]),c_0_51]),c_0_21]),c_0_28]),c_0_14])]),c_0_29]),c_0_23]),c_0_22])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ r2_hidden(X2,k10_yellow_6(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(esk1_2(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk1_2(k10_yellow_6(esk5_0,X1),X2),u1_struct_0(esk5_0))
    | r1_tarski(k10_yellow_6(esk5_0,X1),X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.14/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.030 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t41_yellow_6, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>r1_tarski(k10_yellow_6(X1,X2),k10_yellow_6(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_yellow_6)).
% 0.14/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.39  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.14/0.39  fof(t27_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(r2_waybel_0(X1,X3,X4)=>r2_waybel_0(X1,X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_6)).
% 0.14/0.39  fof(t9_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>~(r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_waybel_0)).
% 0.14/0.39  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.14/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.39  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.14/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.39  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>r1_tarski(k10_yellow_6(X1,X2),k10_yellow_6(X1,X3)))))), inference(assume_negation,[status(cth)],[t41_yellow_6])).
% 0.14/0.39  fof(c_0_10, plain, ![X15]:(~l1_pre_topc(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.39  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((((~v2_struct_0(esk6_0)&v4_orders_2(esk6_0))&v7_waybel_0(esk6_0))&l1_waybel_0(esk6_0,esk5_0))&(m2_yellow_6(esk7_0,esk5_0,esk6_0)&~r1_tarski(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.14/0.39  fof(c_0_12, plain, ![X30, X31, X32]:((((~v2_struct_0(X32)|~m2_yellow_6(X32,X30,X31)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30)))&(v4_orders_2(X32)|~m2_yellow_6(X32,X30,X31)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))))&(v7_waybel_0(X32)|~m2_yellow_6(X32,X30,X31)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))))&(l1_waybel_0(X32,X30)|~m2_yellow_6(X32,X30,X31)|(v2_struct_0(X30)|~l1_struct_0(X30)|v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.14/0.39  cnf(c_0_13, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  fof(c_0_15, plain, ![X33, X34, X35, X36]:(v2_struct_0(X33)|~l1_struct_0(X33)|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33)|(~m2_yellow_6(X35,X33,X34)|(~r2_waybel_0(X33,X35,X36)|r2_waybel_0(X33,X34,X36))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).
% 0.14/0.39  fof(c_0_16, plain, ![X16, X17, X18]:((~r1_waybel_0(X16,X17,X18)|~r2_waybel_0(X16,X17,k6_subset_1(u1_struct_0(X16),X18))|(v2_struct_0(X17)|~l1_waybel_0(X17,X16))|(v2_struct_0(X16)|~l1_struct_0(X16)))&(r2_waybel_0(X16,X17,k6_subset_1(u1_struct_0(X16),X18))|r1_waybel_0(X16,X17,X18)|(v2_struct_0(X17)|~l1_waybel_0(X17,X16))|(v2_struct_0(X16)|~l1_struct_0(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).
% 0.14/0.39  cnf(c_0_17, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_18, negated_conjecture, (m2_yellow_6(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (v7_waybel_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_20, negated_conjecture, (v4_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_21, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.39  cnf(c_0_25, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_26, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_waybel_0(X1,X2,X4)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~r2_waybel_0(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_27, plain, (r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (l1_waybel_0(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22]), c_0_23]), c_0_24])])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22]), c_0_23]), c_0_24])])).
% 0.14/0.39  fof(c_0_30, plain, ![X19, X20, X21, X22, X23, X27]:(((~r2_hidden(X22,X21)|(~m1_connsp_2(X23,X19,X22)|r1_waybel_0(X19,X20,X23))|~m1_subset_1(X22,u1_struct_0(X19))|X21!=k10_yellow_6(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((m1_connsp_2(esk2_4(X19,X20,X21,X22),X19,X22)|r2_hidden(X22,X21)|~m1_subset_1(X22,u1_struct_0(X19))|X21!=k10_yellow_6(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r1_waybel_0(X19,X20,esk2_4(X19,X20,X21,X22))|r2_hidden(X22,X21)|~m1_subset_1(X22,u1_struct_0(X19))|X21!=k10_yellow_6(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))))&((m1_subset_1(esk3_3(X19,X20,X21),u1_struct_0(X19))|X21=k10_yellow_6(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(((m1_connsp_2(esk4_3(X19,X20,X21),X19,esk3_3(X19,X20,X21))|~r2_hidden(esk3_3(X19,X20,X21),X21)|X21=k10_yellow_6(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r1_waybel_0(X19,X20,esk4_3(X19,X20,X21))|~r2_hidden(esk3_3(X19,X20,X21),X21)|X21=k10_yellow_6(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))))&(r2_hidden(esk3_3(X19,X20,X21),X21)|(~m1_connsp_2(X27,X19,esk3_3(X19,X20,X21))|r1_waybel_0(X19,X20,X27))|X21=k10_yellow_6(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.14/0.39  fof(c_0_31, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|m1_subset_1(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.39  fof(c_0_32, plain, ![X28, X29]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28)|m1_subset_1(k10_yellow_6(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,X1)|~r2_waybel_0(esk5_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22]), c_0_23]), c_0_24])])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (r2_waybel_0(esk5_0,esk7_0,k6_subset_1(u1_struct_0(esk5_0),X1))|r1_waybel_0(esk5_0,esk7_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24])]), c_0_29]), c_0_23])).
% 0.14/0.39  cnf(c_0_35, plain, (r1_waybel_0(X4,X5,X3)|v2_struct_0(X5)|v2_struct_0(X4)|~r2_hidden(X1,X2)|~m1_connsp_2(X3,X4,X1)|~m1_subset_1(X1,u1_struct_0(X4))|X2!=k10_yellow_6(X4,X5)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))|~v4_orders_2(X5)|~v7_waybel_0(X5)|~l1_waybel_0(X5,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_36, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  fof(c_0_38, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.39  cnf(c_0_39, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_40, plain, (v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,X3)|~r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,k6_subset_1(u1_struct_0(esk5_0),X1))|r1_waybel_0(esk5_0,esk7_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.39  cnf(c_0_42, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_43, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_44, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X4)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~l1_pre_topc(X1)|~r2_hidden(X4,k10_yellow_6(X1,X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_35, c_0_36])]), c_0_37])).
% 0.14/0.39  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.39  cnf(c_0_46, plain, (m1_connsp_2(esk2_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_47, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(X3,k10_yellow_6(X2,X1))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_pre_topc(X2)|~r1_waybel_0(X2,X1,esk2_4(X2,X1,k10_yellow_6(X2,X1),X3))|~l1_waybel_0(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_37])).
% 0.14/0.39  cnf(c_0_48, negated_conjecture, (r1_waybel_0(esk5_0,esk7_0,X1)|~r1_waybel_0(esk5_0,esk6_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_21]), c_0_24])]), c_0_22]), c_0_23])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (v7_waybel_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22]), c_0_23]), c_0_24])])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (v4_orders_2(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22]), c_0_23]), c_0_24])])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_52, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|r1_tarski(k10_yellow_6(X1,X2),X4)|~m1_connsp_2(X3,X1,esk1_2(k10_yellow_6(X1,X2),X4))|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.39  cnf(c_0_53, plain, (m1_connsp_2(esk2_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)|v2_struct_0(X2)|v2_struct_0(X1)|r2_hidden(X3,k10_yellow_6(X1,X2))|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]), c_0_37])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk5_0,esk7_0))|~r1_waybel_0(esk5_0,esk6_0,esk2_4(esk5_0,esk7_0,k10_yellow_6(esk5_0,esk7_0),X1))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_28]), c_0_14])]), c_0_23]), c_0_29])).
% 0.14/0.39  cnf(c_0_55, plain, (r1_waybel_0(X1,X2,esk2_4(X1,X3,k10_yellow_6(X1,X3),esk1_2(k10_yellow_6(X1,X2),X4)))|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(esk1_2(k10_yellow_6(X1,X2),X4),k10_yellow_6(X1,X3))|r1_tarski(k10_yellow_6(X1,X2),X4)|~v7_waybel_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X2)|~v4_orders_2(X3)|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~l1_waybel_0(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(k10_yellow_6(X1,X2),X4),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.14/0.39  cnf(c_0_56, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k10_yellow_6(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_51]), c_0_14])]), c_0_23])).
% 0.14/0.39  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_2(k10_yellow_6(esk5_0,esk6_0),X1),k10_yellow_6(esk5_0,esk7_0))|r1_tarski(k10_yellow_6(esk5_0,esk6_0),X1)|~m1_subset_1(esk1_2(k10_yellow_6(esk5_0,esk6_0),X1),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_19]), c_0_49]), c_0_20]), c_0_50]), c_0_51]), c_0_21]), c_0_28]), c_0_14])]), c_0_29]), c_0_23]), c_0_22])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (~r1_tarski(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(X2,u1_struct_0(esk5_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk5_0)|~r2_hidden(X2,k10_yellow_6(esk5_0,X1))), inference(spm,[status(thm)],[c_0_36, c_0_56])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, (~m1_subset_1(esk1_2(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.14/0.39  cnf(c_0_62, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(esk1_2(k10_yellow_6(esk5_0,X1),X2),u1_struct_0(esk5_0))|r1_tarski(k10_yellow_6(esk5_0,X1),X2)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_45])).
% 0.14/0.39  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_19]), c_0_20]), c_0_21])]), c_0_22]), c_0_59]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 64
% 0.14/0.39  # Proof object clause steps            : 45
% 0.14/0.39  # Proof object formula steps           : 19
% 0.14/0.39  # Proof object conjectures             : 28
% 0.14/0.39  # Proof object clause conjectures      : 25
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 24
% 0.14/0.39  # Proof object initial formulas used   : 9
% 0.14/0.39  # Proof object generating inferences   : 18
% 0.14/0.39  # Proof object simplifying inferences  : 86
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 9
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 29
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 29
% 0.14/0.39  # Processed clauses                    : 82
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 0
% 0.14/0.39  # ...remaining for further processing  : 82
% 0.14/0.39  # Other redundant clauses eliminated   : 3
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 0
% 0.14/0.39  # Generated clauses                    : 34
% 0.14/0.39  # ...of the previous two non-trivial   : 28
% 0.14/0.39  # Contextual simplify-reflections      : 5
% 0.14/0.39  # Paramodulations                      : 31
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 3
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
% 0.14/0.39  # Current number of processed clauses  : 50
% 0.14/0.39  #    Positive orientable unit clauses  : 11
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 5
% 0.14/0.39  #    Non-unit-clauses                  : 34
% 0.14/0.39  # Current number of unprocessed clauses: 4
% 0.14/0.39  # ...number of literals in the above   : 31
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 29
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1835
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 41
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.39  # Unit Clause-clause subsumption calls : 102
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 3
% 0.14/0.39  # BW rewrite match successes           : 0
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 5042
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.036 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.041 s
% 0.14/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
