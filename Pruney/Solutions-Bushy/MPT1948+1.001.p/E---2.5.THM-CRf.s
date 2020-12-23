%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1948+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:03 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 736 expanded)
%              Number of clauses        :   68 ( 256 expanded)
%              Number of leaves         :   13 ( 181 expanded)
%              Depth                    :   18
%              Number of atoms          :  689 (6360 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   81 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_yellow_6,conjecture,(
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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(t28_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
             => r2_waybel_0(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).

fof(dt_k5_yellow_6,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v6_waybel_0(k5_yellow_6(X1,X2,X3),X1)
        & m1_yellow_6(k5_yellow_6(X1,X2,X3),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_yellow_6)).

fof(dt_m1_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m1_yellow_6(X3,X1,X2)
         => l1_waybel_0(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(t31_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
             => m2_yellow_6(k5_yellow_6(X1,X2,X3),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_6)).

fof(t32_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ( m2_yellow_6(X4,X1,X2)
             => ( X4 = k5_yellow_6(X1,X2,X3)
               => r1_waybel_0(X1,X4,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_yellow_6)).

fof(t10_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ~ r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

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

fof(c_0_13,negated_conjecture,(
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
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( ~ r2_hidden(X3,k10_yellow_6(X1,X2))
                    & ! [X4] :
                        ( m2_yellow_6(X4,X1,X2)
                       => ? [X5] :
                            ( m2_yellow_6(X5,X1,X4)
                            & r2_hidden(X3,k10_yellow_6(X1,X5)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_yellow_6])).

fof(c_0_14,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_15,negated_conjecture,(
    ! [X50] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & ~ v2_struct_0(esk5_0)
      & v4_orders_2(esk5_0)
      & v7_waybel_0(esk5_0)
      & l1_waybel_0(esk5_0,esk4_0)
      & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
      & ~ r2_hidden(esk6_0,k10_yellow_6(esk4_0,esk5_0))
      & ( m2_yellow_6(esk7_1(X50),esk4_0,X50)
        | ~ m2_yellow_6(X50,esk4_0,esk5_0) )
      & ( r2_hidden(esk6_0,k10_yellow_6(esk4_0,esk7_1(X50)))
        | ~ m2_yellow_6(X50,esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).

fof(c_0_16,plain,(
    ! [X6,X7,X8,X9,X10,X14] :
      ( ( ~ r2_hidden(X9,X8)
        | ~ m1_connsp_2(X10,X6,X9)
        | r1_waybel_0(X6,X7,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_connsp_2(esk1_4(X6,X7,X8,X9),X6,X9)
        | r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ r1_waybel_0(X6,X7,esk1_4(X6,X7,X8,X9))
        | r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X8),u1_struct_0(X6))
        | X8 = k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_connsp_2(esk3_3(X6,X7,X8),X6,esk2_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ r1_waybel_0(X6,X7,esk3_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X8)
        | ~ m1_connsp_2(X14,X6,esk2_3(X6,X7,X8))
        | r1_waybel_0(X6,X7,X14)
        | X8 = k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ v4_orders_2(X16)
      | ~ v7_waybel_0(X16)
      | ~ l1_waybel_0(X16,X15)
      | m1_subset_1(k10_yellow_6(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

fof(c_0_18,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v2_struct_0(X26)
        | ~ m2_yellow_6(X26,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24) )
      & ( v4_orders_2(X26)
        | ~ m2_yellow_6(X26,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24) )
      & ( v7_waybel_0(X26)
        | ~ m2_yellow_6(X26,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24) )
      & ( l1_waybel_0(X26,X24)
        | ~ m2_yellow_6(X26,X24,X25)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X30,X31,X32,X33] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | v2_struct_0(X31)
      | ~ v4_orders_2(X31)
      | ~ v7_waybel_0(X31)
      | ~ l1_waybel_0(X31,X30)
      | ~ m2_yellow_6(X32,X30,X31)
      | ~ r2_waybel_0(X30,X32,X33)
      | r2_waybel_0(X30,X31,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

fof(c_0_24,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ l1_struct_0(X34)
      | v2_struct_0(X35)
      | ~ v4_orders_2(X35)
      | ~ v7_waybel_0(X35)
      | ~ l1_waybel_0(X35,X34)
      | ~ r1_waybel_0(X34,X35,X36)
      | r2_waybel_0(X34,X35,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_yellow_6])])])])).

cnf(c_0_25,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m2_yellow_6(esk7_1(X1),esk4_0,X1)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X4)
    | ~ r2_hidden(X4,k10_yellow_6(X1,X2))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk6_0,k10_yellow_6(esk4_0,esk7_1(X1)))
    | ~ m2_yellow_6(X1,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( m1_connsp_2(esk1_4(X1,X2,X3,X4),X1,X4)
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r1_waybel_0(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( l1_waybel_0(esk7_1(X1),esk4_0)
    | v2_struct_0(X1)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( v4_orders_2(esk7_1(X1))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_41,negated_conjecture,
    ( v7_waybel_0(esk7_1(X1))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_42,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_struct_0(esk7_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_43,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk7_1(X1),X2)
    | v2_struct_0(esk7_1(X1))
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ m1_connsp_2(X2,esk4_0,esk6_0)
    | ~ l1_waybel_0(esk7_1(X1),esk4_0)
    | ~ v7_waybel_0(esk7_1(X1))
    | ~ v4_orders_2(esk7_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_20]),c_0_35])]),c_0_27])).

cnf(c_0_44,plain,
    ( m1_connsp_2(esk1_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_22])).

fof(c_0_45,plain,(
    ! [X17,X18,X19] :
      ( ( v6_waybel_0(k5_yellow_6(X17,X18,X19),X17)
        | ~ l1_struct_0(X17)
        | ~ l1_waybel_0(X18,X17) )
      & ( m1_yellow_6(k5_yellow_6(X17,X18,X19),X17,X18)
        | ~ l1_struct_0(X17)
        | ~ l1_waybel_0(X18,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_yellow_6])])])).

cnf(c_0_46,negated_conjecture,
    ( r2_waybel_0(esk4_0,X1,X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(esk4_0,esk7_1(X1),X2)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_47,negated_conjecture,
    ( r2_waybel_0(esk4_0,esk7_1(X1),X2)
    | v2_struct_0(X1)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ r1_waybel_0(esk4_0,esk7_1(X1),X2)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_28])]),c_0_27]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk7_1(X1),esk1_4(esk4_0,X2,k10_yellow_6(esk4_0,X2),esk6_0))
    | r2_hidden(esk6_0,k10_yellow_6(esk4_0,X2))
    | v2_struct_0(esk7_1(X1))
    | v2_struct_0(X2)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ l1_waybel_0(esk7_1(X1),esk4_0)
    | ~ l1_waybel_0(X2,esk4_0)
    | ~ v7_waybel_0(esk7_1(X1))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(esk7_1(X1))
    | ~ v4_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34]),c_0_20]),c_0_35])]),c_0_27])).

fof(c_0_49,plain,(
    ! [X21,X22,X23] :
      ( ~ l1_struct_0(X21)
      | ~ l1_waybel_0(X22,X21)
      | ~ m1_yellow_6(X23,X21,X22)
      | l1_waybel_0(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).

cnf(c_0_50,plain,
    ( m1_yellow_6(k5_yellow_6(X1,X2,X3),X1,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( r2_waybel_0(esk4_0,X1,X2)
    | v2_struct_0(X1)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ r1_waybel_0(esk4_0,esk7_1(X1),X2)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk7_1(X1),esk1_4(esk4_0,X2,k10_yellow_6(esk4_0,X2),esk6_0))
    | r2_hidden(esk6_0,k10_yellow_6(esk4_0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ l1_waybel_0(X2,esk4_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_40]),c_0_39]),c_0_42])).

fof(c_0_54,plain,(
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ l1_struct_0(X37)
      | v2_struct_0(X38)
      | ~ v4_orders_2(X38)
      | ~ v7_waybel_0(X38)
      | ~ l1_waybel_0(X38,X37)
      | ~ r2_waybel_0(X37,X38,X39)
      | m2_yellow_6(k5_yellow_6(X37,X38,X39),X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_yellow_6])])])])).

cnf(c_0_55,plain,
    ( l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( m1_yellow_6(k5_yellow_6(esk4_0,esk5_0,X1),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_28])])).

fof(c_0_57,plain,(
    ! [X40,X41,X42,X43] :
      ( v2_struct_0(X40)
      | ~ l1_struct_0(X40)
      | v2_struct_0(X41)
      | ~ v4_orders_2(X41)
      | ~ v7_waybel_0(X41)
      | ~ l1_waybel_0(X41,X40)
      | ~ m2_yellow_6(X43,X40,X41)
      | X43 != k5_yellow_6(X40,X41,X42)
      | r1_waybel_0(X40,X43,X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_yellow_6])])])])).

cnf(c_0_58,negated_conjecture,
    ( r2_waybel_0(esk4_0,X1,esk1_4(esk4_0,X2,k10_yellow_6(esk4_0,X2),esk6_0))
    | r2_hidden(esk6_0,k10_yellow_6(esk4_0,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m2_yellow_6(X1,esk4_0,esk5_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ l1_waybel_0(X2,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m2_yellow_6(k5_yellow_6(X1,X2,X3),X1,X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r2_waybel_0(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( l1_waybel_0(k5_yellow_6(esk4_0,esk5_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_28]),c_0_51])])).

cnf(c_0_61,negated_conjecture,
    ( v7_waybel_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_64,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r2_waybel_0(X27,X28,X29)
        | ~ r1_waybel_0(X27,X28,k6_subset_1(u1_struct_0(X27),X29))
        | v2_struct_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27) )
      & ( r1_waybel_0(X27,X28,k6_subset_1(u1_struct_0(X27),X29))
        | r2_waybel_0(X27,X28,X29)
        | v2_struct_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_waybel_0(X1,X3,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | X3 != k5_yellow_6(X1,X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r2_waybel_0(esk4_0,k5_yellow_6(esk4_0,esk5_0,X1),esk1_4(esk4_0,X2,k10_yellow_6(esk4_0,X2),esk6_0))
    | r2_hidden(esk6_0,k10_yellow_6(esk4_0,X2))
    | v2_struct_0(k5_yellow_6(esk4_0,esk5_0,X1))
    | v2_struct_0(X2)
    | ~ r2_waybel_0(esk4_0,esk5_0,X1)
    | ~ l1_waybel_0(X2,esk4_0)
    | ~ v7_waybel_0(k5_yellow_6(esk4_0,esk5_0,X1))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(k5_yellow_6(esk4_0,esk5_0,X1))
    | ~ v4_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_28]),c_0_51]),c_0_61]),c_0_62])]),c_0_63]),c_0_27])).

cnf(c_0_67,plain,
    ( v7_waybel_0(k5_yellow_6(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_59])).

cnf(c_0_68,plain,
    ( v4_orders_2(k5_yellow_6(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_59])).

cnf(c_0_69,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,plain,
    ( r1_waybel_0(X1,k5_yellow_6(X1,X2,X3),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m2_yellow_6(k5_yellow_6(X1,X2,X3),X1,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r2_waybel_0(esk4_0,k5_yellow_6(esk4_0,esk5_0,X1),esk1_4(esk4_0,X2,k10_yellow_6(esk4_0,X2),esk6_0))
    | r2_hidden(esk6_0,k10_yellow_6(esk4_0,X2))
    | v2_struct_0(k5_yellow_6(esk4_0,esk5_0,X1))
    | v2_struct_0(X2)
    | ~ r2_waybel_0(esk4_0,esk5_0,X1)
    | ~ l1_waybel_0(X2,esk4_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(k5_yellow_6(esk4_0,esk5_0,X1))
    | ~ v4_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_28]),c_0_51]),c_0_61]),c_0_62])]),c_0_27]),c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( v4_orders_2(k5_yellow_6(X1,esk5_0,X2))
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,esk5_0,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_61]),c_0_62])]),c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( r2_waybel_0(esk4_0,esk5_0,X1)
    | r1_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51]),c_0_63]),c_0_27])).

cnf(c_0_74,plain,
    ( r1_waybel_0(X1,k5_yellow_6(X1,X2,X3),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_59])).

cnf(c_0_75,negated_conjecture,
    ( r2_waybel_0(esk4_0,k5_yellow_6(esk4_0,esk5_0,X1),esk1_4(esk4_0,X2,k10_yellow_6(esk4_0,X2),esk6_0))
    | r2_hidden(esk6_0,k10_yellow_6(esk4_0,X2))
    | v2_struct_0(k5_yellow_6(esk4_0,esk5_0,X1))
    | v2_struct_0(X2)
    | ~ r2_waybel_0(esk4_0,esk5_0,X1)
    | ~ l1_waybel_0(X2,esk4_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_28]),c_0_51])]),c_0_27])).

cnf(c_0_76,negated_conjecture,
    ( r2_waybel_0(esk4_0,esk5_0,X1)
    | r1_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_28])])).

cnf(c_0_77,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( r1_waybel_0(esk4_0,k5_yellow_6(esk4_0,esk5_0,X1),X1)
    | ~ r2_waybel_0(esk4_0,esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_51]),c_0_28]),c_0_61]),c_0_62])]),c_0_63]),c_0_27])).

cnf(c_0_79,negated_conjecture,
    ( r2_waybel_0(esk4_0,k5_yellow_6(esk4_0,esk5_0,X1),esk1_4(esk4_0,X2,k10_yellow_6(esk4_0,X2),esk6_0))
    | r1_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1))
    | r2_hidden(esk6_0,k10_yellow_6(esk4_0,X2))
    | v2_struct_0(k5_yellow_6(esk4_0,esk5_0,X1))
    | v2_struct_0(X2)
    | ~ l1_waybel_0(X2,esk4_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k10_yellow_6(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_struct_0(k5_yellow_6(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_59])).

cnf(c_0_82,negated_conjecture,
    ( v2_struct_0(k5_yellow_6(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1)))
    | ~ r2_waybel_0(esk4_0,k5_yellow_6(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1)),X1)
    | ~ r2_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_28]),c_0_60])]),c_0_27])).

cnf(c_0_83,negated_conjecture,
    ( r2_waybel_0(esk4_0,k5_yellow_6(esk4_0,esk5_0,X1),esk1_4(esk4_0,esk5_0,k10_yellow_6(esk4_0,esk5_0),esk6_0))
    | r1_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1))
    | v2_struct_0(k5_yellow_6(esk4_0,esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_51]),c_0_61]),c_0_62])]),c_0_80]),c_0_63])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_waybel_0(esk4_0,k5_yellow_6(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1)),X1)
    | ~ r2_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_28]),c_0_51]),c_0_61]),c_0_62])]),c_0_27]),c_0_63])).

cnf(c_0_85,negated_conjecture,
    ( r2_waybel_0(esk4_0,k5_yellow_6(esk4_0,esk5_0,X1),esk1_4(esk4_0,esk5_0,k10_yellow_6(esk4_0,esk5_0),esk6_0))
    | r1_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_83]),c_0_28]),c_0_51]),c_0_61]),c_0_62])]),c_0_27]),c_0_63]),c_0_76])).

fof(c_0_86,plain,(
    ! [X44,X45,X46] :
      ( ( ~ r1_waybel_0(X44,X45,X46)
        | ~ r2_waybel_0(X44,X45,k6_subset_1(u1_struct_0(X44),X46))
        | v2_struct_0(X45)
        | ~ l1_waybel_0(X45,X44)
        | v2_struct_0(X44)
        | ~ l1_struct_0(X44) )
      & ( r2_waybel_0(X44,X45,k6_subset_1(u1_struct_0(X44),X46))
        | r1_waybel_0(X44,X45,X46)
        | v2_struct_0(X45)
        | ~ l1_waybel_0(X45,X44)
        | v2_struct_0(X44)
        | ~ l1_struct_0(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).

cnf(c_0_87,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),k6_subset_1(u1_struct_0(esk4_0),esk1_4(esk4_0,esk5_0,k10_yellow_6(esk4_0,esk5_0),esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_76])).

cnf(c_0_88,plain,
    ( r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_89,plain,
    ( r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,esk1_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),esk1_4(esk4_0,esk5_0,k10_yellow_6(esk4_0,esk5_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_87]),c_0_28]),c_0_51])]),c_0_63]),c_0_27])).

cnf(c_0_91,negated_conjecture,
    ( r2_waybel_0(esk4_0,esk5_0,k6_subset_1(u1_struct_0(esk4_0),X1))
    | r1_waybel_0(esk4_0,esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_51]),c_0_63]),c_0_27]),c_0_28])])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_waybel_0(X2,X3,esk1_4(X2,X3,k10_yellow_6(X2,X3),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_89]),c_0_22])).

cnf(c_0_93,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,esk1_4(esk4_0,esk5_0,k10_yellow_6(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_34]),c_0_51]),c_0_61]),c_0_62]),c_0_20]),c_0_35])]),c_0_80]),c_0_27]),c_0_63]),
    [proof]).

%------------------------------------------------------------------------------
