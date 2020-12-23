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
% DateTime   : Thu Dec  3 11:22:07 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  106 (2283 expanded)
%              Number of clauses        :   75 ( 733 expanded)
%              Number of leaves         :   15 ( 595 expanded)
%              Depth                    :   23
%              Number of atoms          :  942 (26029 expanded)
%              Number of equality atoms :   31 ( 116 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal clause size      :   81 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ? [X3] :
                ( m2_yellow_6(X3,X1,X2)
                & v3_yellow_6(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

fof(d19_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ( v3_yellow_6(X2,X1)
          <=> k10_yellow_6(X1,X2) != k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

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

fof(t29_waybel_9,axiom,(
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
             => ( r2_hidden(X3,k10_yellow_6(X1,X2))
               => r3_waybel_9(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

fof(l37_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r3_waybel_9(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t36_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ~ ( r2_hidden(X2,k6_yellow_6(X1))
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r3_waybel_9(X1,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( v1_compts_1(X1)
        <=> ! [X2] :
              ( ( ~ v2_struct_0(X2)
                & v4_orders_2(X2)
                & v7_waybel_0(X2)
                & l1_waybel_0(X2,X1) )
             => ? [X3] :
                  ( m2_yellow_6(X3,X1,X2)
                  & v3_yellow_6(X3,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_yellow19])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | ~ r1_tarski(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_17,plain,(
    ! [X37,X38,X39] :
      ( ( m2_yellow_6(esk4_3(X37,X38,X39),X37,X38)
        | ~ r3_waybel_9(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | v2_struct_0(X38)
        | ~ v4_orders_2(X38)
        | ~ v7_waybel_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(X39,k10_yellow_6(X37,esk4_3(X37,X38,X39)))
        | ~ r3_waybel_9(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | v2_struct_0(X38)
        | ~ v4_orders_2(X38)
        | ~ v7_waybel_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

fof(c_0_18,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_struct_0(X27)
        | ~ m2_yellow_6(X27,X25,X26)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25) )
      & ( v4_orders_2(X27)
        | ~ m2_yellow_6(X27,X25,X26)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25) )
      & ( v7_waybel_0(X27)
        | ~ m2_yellow_6(X27,X25,X26)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25) )
      & ( l1_waybel_0(X27,X25)
        | ~ m2_yellow_6(X27,X25,X26)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

fof(c_0_19,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_20,plain,(
    ! [X14,X15,X16,X17,X18,X22] :
      ( ( ~ r2_hidden(X17,X16)
        | ~ m1_connsp_2(X18,X14,X17)
        | r1_waybel_0(X14,X15,X18)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | X16 != k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_connsp_2(esk1_4(X14,X15,X16,X17),X14,X17)
        | r2_hidden(X17,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | X16 != k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r1_waybel_0(X14,X15,esk1_4(X14,X15,X16,X17))
        | r2_hidden(X17,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | X16 != k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_connsp_2(esk3_3(X14,X15,X16),X14,esk2_3(X14,X15,X16))
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r1_waybel_0(X14,X15,esk3_3(X14,X15,X16))
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ m1_connsp_2(X22,X14,esk2_3(X14,X15,X16))
        | r1_waybel_0(X14,X15,X22)
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_21,negated_conjecture,(
    ! [X51,X52] :
      ( ~ v2_struct_0(esk8_0)
      & v2_pre_topc(esk8_0)
      & l1_pre_topc(esk8_0)
      & ( ~ v2_struct_0(esk9_0)
        | ~ v1_compts_1(esk8_0) )
      & ( v4_orders_2(esk9_0)
        | ~ v1_compts_1(esk8_0) )
      & ( v7_waybel_0(esk9_0)
        | ~ v1_compts_1(esk8_0) )
      & ( l1_waybel_0(esk9_0,esk8_0)
        | ~ v1_compts_1(esk8_0) )
      & ( ~ m2_yellow_6(X51,esk8_0,esk9_0)
        | ~ v3_yellow_6(X51,esk8_0)
        | ~ v1_compts_1(esk8_0) )
      & ( m2_yellow_6(esk10_1(X52),esk8_0,X52)
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ v7_waybel_0(X52)
        | ~ l1_waybel_0(X52,esk8_0)
        | v1_compts_1(esk8_0) )
      & ( v3_yellow_6(esk10_1(X52),esk8_0)
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ v7_waybel_0(X52)
        | ~ l1_waybel_0(X52,esk8_0)
        | v1_compts_1(esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk4_3(X2,X3,X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X28,X29] :
      ( ( ~ v3_yellow_6(X29,X28)
        | k10_yellow_6(X28,X29) != k1_xboole_0
        | v2_struct_0(X29)
        | ~ v4_orders_2(X29)
        | ~ v7_waybel_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( k10_yellow_6(X28,X29) = k1_xboole_0
        | v3_yellow_6(X29,X28)
        | v2_struct_0(X29)
        | ~ v4_orders_2(X29)
        | ~ v7_waybel_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

fof(c_0_25,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_26,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( m2_yellow_6(esk4_3(X1,X2,X3),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( l1_waybel_0(X1,X2)
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

fof(c_0_32,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | m1_subset_1(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_33,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ v4_orders_2(X24)
      | ~ v7_waybel_0(X24)
      | ~ l1_waybel_0(X24,X23)
      | m1_subset_1(k10_yellow_6(X23,X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r1_waybel_0(X1,X2,X4)
    | X3 = k10_yellow_6(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X4,X1,esk2_3(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k10_yellow_6(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk8_0,esk9_0)
    | ~ v3_yellow_6(X1,esk8_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( v4_orders_2(esk9_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( v7_waybel_0(esk9_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( l1_waybel_0(esk9_0,esk8_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(k10_yellow_6(X1,esk4_3(X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_46,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_48,plain,
    ( v4_orders_2(esk4_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_49,plain,
    ( v7_waybel_0(esk4_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_28])).

cnf(c_0_50,plain,
    ( l1_waybel_0(esk4_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_28])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_struct_0(esk4_3(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28])).

fof(c_0_52,plain,(
    ! [X33,X34,X35,X36] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ v4_orders_2(X34)
      | ~ v7_waybel_0(X34)
      | ~ l1_waybel_0(X34,X33)
      | ~ m2_yellow_6(X35,X33,X34)
      | ~ m1_subset_1(X36,u1_struct_0(X33))
      | ~ r3_waybel_9(X33,X35,X36)
      | r3_waybel_9(X33,X34,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

fof(c_0_53,plain,(
    ! [X30,X31,X32] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v4_orders_2(X31)
      | ~ v7_waybel_0(X31)
      | ~ l1_waybel_0(X31,X30)
      | ~ m1_subset_1(X32,u1_struct_0(X30))
      | ~ r2_hidden(X32,k10_yellow_6(X30,X31))
      | r3_waybel_9(X30,X31,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,plain,
    ( X1 = k10_yellow_6(X2,X3)
    | r1_waybel_0(X2,X3,esk1_4(X2,X4,X5,esk2_3(X2,X3,X1)))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_hidden(esk2_3(X2,X3,X1),X5)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | X5 != k10_yellow_6(X2,X4)
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_waybel_0(X4,X2)
    | ~ v7_waybel_0(X3)
    | ~ v7_waybel_0(X4)
    | ~ v4_orders_2(X3)
    | ~ v4_orders_2(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_compts_1(esk8_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v3_yellow_6(esk4_3(esk8_0,esk9_0,X1),esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_38]),c_0_39])]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_59,plain,
    ( v3_yellow_6(esk4_3(X1,X2,X3),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),c_0_48]),c_0_49]),c_0_50]),c_0_51])).

fof(c_0_60,plain,(
    ! [X41,X42] :
      ( ( m1_subset_1(esk5_2(X41,X42),u1_struct_0(X41))
        | v2_struct_0(X42)
        | ~ v4_orders_2(X42)
        | ~ v7_waybel_0(X42)
        | ~ l1_waybel_0(X42,X41)
        | ~ v1_compts_1(X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( r3_waybel_9(X41,X42,esk5_2(X41,X42))
        | v2_struct_0(X42)
        | ~ v4_orders_2(X42)
        | ~ v7_waybel_0(X42)
        | ~ l1_waybel_0(X42,X41)
        | ~ v1_compts_1(X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).

cnf(c_0_61,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( m2_yellow_6(esk10_1(X1),esk8_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk8_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r3_waybel_9(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,k10_yellow_6(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,k10_yellow_6(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( X1 = k10_yellow_6(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | r2_hidden(esk2_3(X2,X3,X1),X4)
    | X4 != k10_yellow_6(X2,X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_36])).

fof(c_0_66,plain,(
    ! [X7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_compts_1(esk8_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_38]),c_0_39])]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_68,plain,
    ( r3_waybel_9(X1,X2,esk5_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | r3_waybel_9(esk8_0,X1,X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,esk10_1(X1),X2)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_70,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,k10_yellow_6(X1,X2)) ),
    inference(csr,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( X1 = k10_yellow_6(X2,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | r2_hidden(esk2_3(X2,X3,X1),k10_yellow_6(X2,X4))
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | k10_yellow_6(X2,X4) != k10_yellow_6(X2,X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_waybel_0(X4,X2)
    | ~ v7_waybel_0(X3)
    | ~ v7_waybel_0(X4)
    | ~ v4_orders_2(X3)
    | ~ v4_orders_2(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_55])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_compts_1(esk8_0)
    | ~ m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_38]),c_0_39])]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_74,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | r3_waybel_9(esk8_0,X1,X2)
    | v2_struct_0(esk10_1(X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk10_1(X1),esk8_0)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(esk10_1(X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk10_1(X1))
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(X2,k10_yellow_6(esk8_0,esk10_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_76,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),k10_yellow_6(X1,X3))
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | k10_yellow_6(X1,X3) != k10_yellow_6(X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_compts_1(esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_38]),c_0_39])]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

fof(c_0_78,plain,(
    ! [X44,X45,X48] :
      ( ( m1_subset_1(esk6_2(X44,X45),u1_struct_0(X44))
        | ~ r2_hidden(X45,k6_yellow_6(X44))
        | v2_struct_0(X45)
        | ~ v4_orders_2(X45)
        | ~ v7_waybel_0(X45)
        | ~ l1_waybel_0(X45,X44)
        | ~ v1_compts_1(X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( r3_waybel_9(X44,X45,esk6_2(X44,X45))
        | ~ r2_hidden(X45,k6_yellow_6(X44))
        | v2_struct_0(X45)
        | ~ v4_orders_2(X45)
        | ~ v7_waybel_0(X45)
        | ~ l1_waybel_0(X45,X44)
        | ~ v1_compts_1(X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( ~ v2_struct_0(esk7_1(X44))
        | v1_compts_1(X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( v4_orders_2(esk7_1(X44))
        | v1_compts_1(X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( v7_waybel_0(esk7_1(X44))
        | v1_compts_1(X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( l1_waybel_0(esk7_1(X44),X44)
        | v1_compts_1(X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( r2_hidden(esk7_1(X44),k6_yellow_6(X44))
        | v1_compts_1(X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( ~ m1_subset_1(X48,u1_struct_0(X44))
        | ~ r3_waybel_9(X44,esk7_1(X44),X48)
        | v1_compts_1(X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_yellow19])])])])])])).

cnf(c_0_79,negated_conjecture,
    ( k10_yellow_6(esk8_0,X1) = k1_xboole_0
    | r3_waybel_9(esk8_0,X2,esk2_3(esk8_0,X1,k1_xboole_0))
    | v2_struct_0(esk10_1(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(esk2_3(esk8_0,X1,k1_xboole_0),k1_xboole_0)
    | k10_yellow_6(esk8_0,esk10_1(X2)) != k10_yellow_6(esk8_0,X1)
    | ~ l1_waybel_0(esk10_1(X2),esk8_0)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(esk10_1(X2))
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk10_1(X2))
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk2_3(esk8_0,X1,k1_xboole_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_38]),c_0_39])]),c_0_77]),c_0_40])).

cnf(c_0_80,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk7_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk10_1(X1)) = k1_xboole_0
    | r3_waybel_9(esk8_0,X1,esk2_3(esk8_0,esk10_1(X1),k1_xboole_0))
    | v2_struct_0(esk10_1(X1))
    | v2_struct_0(X1)
    | r2_hidden(esk2_3(esk8_0,esk10_1(X1),k1_xboole_0),k1_xboole_0)
    | ~ l1_waybel_0(esk10_1(X1),esk8_0)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(esk10_1(X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk10_1(X1))
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(esk2_3(esk8_0,esk10_1(X1),k1_xboole_0),u1_struct_0(esk8_0)) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))) = k1_xboole_0
    | v2_struct_0(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0))
    | r2_hidden(esk2_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),k1_xboole_0)
    | ~ l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)
    | ~ l1_waybel_0(esk7_1(esk8_0),esk8_0)
    | ~ v7_waybel_0(esk10_1(esk7_1(esk8_0)))
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | ~ v4_orders_2(esk7_1(esk8_0))
    | ~ m1_subset_1(esk2_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_38]),c_0_39])]),c_0_77]),c_0_40])).

cnf(c_0_83,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))) = k1_xboole_0
    | v2_struct_0(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0))
    | ~ l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)
    | ~ l1_waybel_0(esk7_1(esk8_0),esk8_0)
    | ~ v7_waybel_0(esk10_1(esk7_1(esk8_0)))
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | ~ v4_orders_2(esk7_1(esk8_0))
    | ~ m1_subset_1(esk2_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_82]),c_0_47])])).

cnf(c_0_84,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))) = k1_xboole_0
    | v2_struct_0(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0))
    | ~ l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)
    | ~ l1_waybel_0(esk7_1(esk8_0),esk8_0)
    | ~ v7_waybel_0(esk10_1(esk7_1(esk8_0)))
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | ~ v4_orders_2(esk7_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_36]),c_0_38]),c_0_39]),c_0_72])]),c_0_40])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0))
    | ~ v3_yellow_6(esk10_1(esk7_1(esk8_0)),esk8_0)
    | ~ l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)
    | ~ l1_waybel_0(esk7_1(esk8_0),esk8_0)
    | ~ v7_waybel_0(esk10_1(esk7_1(esk8_0)))
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | ~ v4_orders_2(esk7_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_87,negated_conjecture,
    ( v3_yellow_6(esk10_1(X1),esk8_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk8_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( v2_struct_0(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0))
    | ~ l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)
    | ~ l1_waybel_0(esk7_1(esk8_0),esk8_0)
    | ~ v7_waybel_0(esk10_1(esk7_1(esk8_0)))
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | ~ v4_orders_2(esk7_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | l1_waybel_0(esk10_1(X1),esk8_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_62]),c_0_40])).

cnf(c_0_90,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_struct_0(esk10_1(X1))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_62]),c_0_40])).

cnf(c_0_91,negated_conjecture,
    ( v2_struct_0(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0))
    | ~ l1_waybel_0(esk7_1(esk8_0),esk8_0)
    | ~ v7_waybel_0(esk10_1(esk7_1(esk8_0)))
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | ~ v4_orders_2(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( v2_struct_0(esk7_1(esk8_0))
    | ~ l1_waybel_0(esk7_1(esk8_0),esk8_0)
    | ~ v7_waybel_0(esk10_1(esk7_1(esk8_0)))
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | ~ v4_orders_2(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_77])).

cnf(c_0_93,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v7_waybel_0(esk10_1(X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_62]),c_0_40])).

cnf(c_0_94,negated_conjecture,
    ( v2_struct_0(esk7_1(esk8_0))
    | ~ l1_waybel_0(esk7_1(esk8_0),esk8_0)
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | ~ v4_orders_2(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_77])).

cnf(c_0_95,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v4_orders_2(esk10_1(X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_62]),c_0_40])).

cnf(c_0_96,negated_conjecture,
    ( v2_struct_0(esk7_1(esk8_0))
    | ~ l1_waybel_0(esk7_1(esk8_0),esk8_0)
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_77])).

cnf(c_0_97,plain,
    ( l1_waybel_0(esk7_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_98,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk7_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_99,negated_conjecture,
    ( v2_struct_0(esk7_1(esk8_0))
    | ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_38]),c_0_39])]),c_0_77]),c_0_40])).

cnf(c_0_100,negated_conjecture,
    ( ~ v7_waybel_0(esk7_1(esk8_0))
    | ~ v4_orders_2(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_38]),c_0_39])]),c_0_77]),c_0_40])).

cnf(c_0_101,plain,
    ( v7_waybel_0(esk7_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_102,negated_conjecture,
    ( ~ v4_orders_2(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_38]),c_0_39])]),c_0_77]),c_0_40])).

cnf(c_0_103,plain,
    ( v4_orders_2(esk7_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_104,negated_conjecture,
    ( ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_38]),c_0_39])]),c_0_77]),c_0_40])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_28]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.41  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.14/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.41  #
% 0.14/0.41  # Preprocessing time       : 0.030 s
% 0.14/0.41  # Presaturation interreduction done
% 0.14/0.41  
% 0.14/0.41  # Proof found!
% 0.14/0.41  # SZS status Theorem
% 0.14/0.41  # SZS output start CNFRefutation
% 0.14/0.41  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 0.14/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.41  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.14/0.41  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.14/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.41  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.14/0.41  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.14/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.41  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.14/0.41  fof(t31_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 0.14/0.41  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.14/0.41  fof(l37_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l37_yellow19)).
% 0.14/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.14/0.41  fof(t36_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>~((r2_hidden(X2,k6_yellow_6(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r3_waybel_9(X1,X2,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_yellow19)).
% 0.14/0.41  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.14/0.41  fof(c_0_16, plain, ![X11, X12]:(~r2_hidden(X11,X12)|~r1_tarski(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.41  fof(c_0_17, plain, ![X37, X38, X39]:((m2_yellow_6(esk4_3(X37,X38,X39),X37,X38)|~r3_waybel_9(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|(v2_struct_0(X38)|~v4_orders_2(X38)|~v7_waybel_0(X38)|~l1_waybel_0(X38,X37))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(r2_hidden(X39,k10_yellow_6(X37,esk4_3(X37,X38,X39)))|~r3_waybel_9(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|(v2_struct_0(X38)|~v4_orders_2(X38)|~v7_waybel_0(X38)|~l1_waybel_0(X38,X37))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.14/0.41  fof(c_0_18, plain, ![X25, X26, X27]:((((~v2_struct_0(X27)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25)))&(v4_orders_2(X27)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))))&(v7_waybel_0(X27)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))))&(l1_waybel_0(X27,X25)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.14/0.41  fof(c_0_19, plain, ![X13]:(~l1_pre_topc(X13)|l1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.41  fof(c_0_20, plain, ![X14, X15, X16, X17, X18, X22]:(((~r2_hidden(X17,X16)|(~m1_connsp_2(X18,X14,X17)|r1_waybel_0(X14,X15,X18))|~m1_subset_1(X17,u1_struct_0(X14))|X16!=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&((m1_connsp_2(esk1_4(X14,X15,X16,X17),X14,X17)|r2_hidden(X17,X16)|~m1_subset_1(X17,u1_struct_0(X14))|X16!=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r1_waybel_0(X14,X15,esk1_4(X14,X15,X16,X17))|r2_hidden(X17,X16)|~m1_subset_1(X17,u1_struct_0(X14))|X16!=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))))&((m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(((m1_connsp_2(esk3_3(X14,X15,X16),X14,esk2_3(X14,X15,X16))|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r1_waybel_0(X14,X15,esk3_3(X14,X15,X16))|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))))&(r2_hidden(esk2_3(X14,X15,X16),X16)|(~m1_connsp_2(X22,X14,esk2_3(X14,X15,X16))|r1_waybel_0(X14,X15,X22))|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.14/0.41  fof(c_0_21, negated_conjecture, ![X51, X52]:(((~v2_struct_0(esk8_0)&v2_pre_topc(esk8_0))&l1_pre_topc(esk8_0))&((((((~v2_struct_0(esk9_0)|~v1_compts_1(esk8_0))&(v4_orders_2(esk9_0)|~v1_compts_1(esk8_0)))&(v7_waybel_0(esk9_0)|~v1_compts_1(esk8_0)))&(l1_waybel_0(esk9_0,esk8_0)|~v1_compts_1(esk8_0)))&(~m2_yellow_6(X51,esk8_0,esk9_0)|~v3_yellow_6(X51,esk8_0)|~v1_compts_1(esk8_0)))&((m2_yellow_6(esk10_1(X52),esk8_0,X52)|(v2_struct_0(X52)|~v4_orders_2(X52)|~v7_waybel_0(X52)|~l1_waybel_0(X52,esk8_0))|v1_compts_1(esk8_0))&(v3_yellow_6(esk10_1(X52),esk8_0)|(v2_struct_0(X52)|~v4_orders_2(X52)|~v7_waybel_0(X52)|~l1_waybel_0(X52,esk8_0))|v1_compts_1(esk8_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.14/0.41  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.41  cnf(c_0_23, plain, (r2_hidden(X1,k10_yellow_6(X2,esk4_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  fof(c_0_24, plain, ![X28, X29]:((~v3_yellow_6(X29,X28)|k10_yellow_6(X28,X29)!=k1_xboole_0|(v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(k10_yellow_6(X28,X29)=k1_xboole_0|v3_yellow_6(X29,X28)|(v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.14/0.41  fof(c_0_25, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.41  cnf(c_0_26, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.41  cnf(c_0_27, plain, (m2_yellow_6(esk4_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_28, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.41  cnf(c_0_29, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.41  cnf(c_0_30, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.41  cnf(c_0_31, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.41  fof(c_0_32, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|m1_subset_1(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.41  fof(c_0_33, plain, ![X23, X24]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23)|m1_subset_1(k10_yellow_6(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.14/0.41  cnf(c_0_34, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r1_waybel_0(X1,X2,X4)|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X4,X1,esk2_3(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.41  cnf(c_0_35, plain, (m1_connsp_2(esk1_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.41  cnf(c_0_36, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.41  cnf(c_0_37, negated_conjecture, (~m2_yellow_6(X1,esk8_0,esk9_0)|~v3_yellow_6(X1,esk8_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_41, negated_conjecture, (v4_orders_2(esk9_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_42, negated_conjecture, (v7_waybel_0(esk9_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_43, negated_conjecture, (l1_waybel_0(esk9_0,esk8_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk9_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_45, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(k10_yellow_6(X1,esk4_3(X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.41  cnf(c_0_46, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.41  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.41  cnf(c_0_48, plain, (v4_orders_2(esk4_3(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.14/0.41  cnf(c_0_49, plain, (v7_waybel_0(esk4_3(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_27]), c_0_28])).
% 0.14/0.41  cnf(c_0_50, plain, (l1_waybel_0(esk4_3(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_28])).
% 0.14/0.41  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~v2_struct_0(esk4_3(X1,X2,X3))|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_28])).
% 0.14/0.41  fof(c_0_52, plain, ![X33, X34, X35, X36]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33)|(~m2_yellow_6(X35,X33,X34)|(~m1_subset_1(X36,u1_struct_0(X33))|(~r3_waybel_9(X33,X35,X36)|r3_waybel_9(X33,X34,X36)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).
% 0.14/0.41  fof(c_0_53, plain, ![X30, X31, X32]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30)|(~m1_subset_1(X32,u1_struct_0(X30))|(~r2_hidden(X32,k10_yellow_6(X30,X31))|r3_waybel_9(X30,X31,X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.14/0.41  cnf(c_0_54, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.41  cnf(c_0_55, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.41  cnf(c_0_56, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk1_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.41  cnf(c_0_57, plain, (X1=k10_yellow_6(X2,X3)|r1_waybel_0(X2,X3,esk1_4(X2,X4,X5,esk2_3(X2,X3,X1)))|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk2_3(X2,X3,X1),X5)|r2_hidden(esk2_3(X2,X3,X1),X1)|X5!=k10_yellow_6(X2,X4)|~l1_waybel_0(X3,X2)|~l1_waybel_0(X4,X2)|~v7_waybel_0(X3)|~v7_waybel_0(X4)|~v4_orders_2(X3)|~v4_orders_2(X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.14/0.41  cnf(c_0_58, negated_conjecture, (~v1_compts_1(esk8_0)|~r3_waybel_9(esk8_0,esk9_0,X1)|~v3_yellow_6(esk4_3(esk8_0,esk9_0,X1),esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_27]), c_0_38]), c_0_39])]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.14/0.41  cnf(c_0_59, plain, (v3_yellow_6(esk4_3(X1,X2,X3),X1)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), c_0_48]), c_0_49]), c_0_50]), c_0_51])).
% 0.14/0.41  fof(c_0_60, plain, ![X41, X42]:((m1_subset_1(esk5_2(X41,X42),u1_struct_0(X41))|(v2_struct_0(X42)|~v4_orders_2(X42)|~v7_waybel_0(X42)|~l1_waybel_0(X42,X41))|~v1_compts_1(X41)|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(r3_waybel_9(X41,X42,esk5_2(X41,X42))|(v2_struct_0(X42)|~v4_orders_2(X42)|~v7_waybel_0(X42)|~l1_waybel_0(X42,X41))|~v1_compts_1(X41)|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).
% 0.14/0.41  cnf(c_0_61, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~r3_waybel_9(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.41  cnf(c_0_62, negated_conjecture, (m2_yellow_6(esk10_1(X1),esk8_0,X1)|v2_struct_0(X1)|v1_compts_1(esk8_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_63, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.41  cnf(c_0_64, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.41  cnf(c_0_65, plain, (X1=k10_yellow_6(X2,X3)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|r2_hidden(esk2_3(X2,X3,X1),X4)|X4!=k10_yellow_6(X2,X3)|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_36])).
% 0.14/0.41  fof(c_0_66, plain, ![X7]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.14/0.41  cnf(c_0_67, negated_conjecture, (~v1_compts_1(esk8_0)|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_38]), c_0_39])]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.14/0.41  cnf(c_0_68, plain, (r3_waybel_9(X1,X2,esk5_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.14/0.41  cnf(c_0_69, negated_conjecture, (v1_compts_1(esk8_0)|r3_waybel_9(esk8_0,X1,X2)|v2_struct_0(X1)|~r3_waybel_9(esk8_0,esk10_1(X1),X2)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_38]), c_0_39])]), c_0_40])).
% 0.14/0.41  cnf(c_0_70, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(csr,[status(thm)],[c_0_63, c_0_64])).
% 0.14/0.41  cnf(c_0_71, plain, (X1=k10_yellow_6(X2,X3)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|r2_hidden(esk2_3(X2,X3,X1),k10_yellow_6(X2,X4))|r2_hidden(esk2_3(X2,X3,X1),X1)|k10_yellow_6(X2,X4)!=k10_yellow_6(X2,X3)|~l1_waybel_0(X3,X2)|~l1_waybel_0(X4,X2)|~v7_waybel_0(X3)|~v7_waybel_0(X4)|~v4_orders_2(X3)|~v4_orders_2(X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_65, c_0_55])).
% 0.14/0.41  cnf(c_0_72, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.14/0.41  cnf(c_0_73, negated_conjecture, (~v1_compts_1(esk8_0)|~m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_38]), c_0_39])]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.14/0.41  cnf(c_0_74, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.14/0.41  cnf(c_0_75, negated_conjecture, (v1_compts_1(esk8_0)|r3_waybel_9(esk8_0,X1,X2)|v2_struct_0(esk10_1(X1))|v2_struct_0(X1)|~l1_waybel_0(esk10_1(X1),esk8_0)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(esk10_1(X1))|~v7_waybel_0(X1)|~v4_orders_2(esk10_1(X1))|~v4_orders_2(X1)|~r2_hidden(X2,k10_yellow_6(esk8_0,esk10_1(X1)))|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_38]), c_0_39])]), c_0_40])).
% 0.14/0.41  cnf(c_0_76, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk2_3(X1,X2,k1_xboole_0),k10_yellow_6(X1,X3))|r2_hidden(esk2_3(X1,X2,k1_xboole_0),k1_xboole_0)|k10_yellow_6(X1,X3)!=k10_yellow_6(X1,X2)|~l1_waybel_0(X2,X1)|~l1_waybel_0(X3,X1)|~v7_waybel_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X2)|~v4_orders_2(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.14/0.41  cnf(c_0_77, negated_conjecture, (~v1_compts_1(esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_38]), c_0_39])]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.14/0.41  fof(c_0_78, plain, ![X44, X45, X48]:(((m1_subset_1(esk6_2(X44,X45),u1_struct_0(X44))|~r2_hidden(X45,k6_yellow_6(X44))|(v2_struct_0(X45)|~v4_orders_2(X45)|~v7_waybel_0(X45)|~l1_waybel_0(X45,X44))|~v1_compts_1(X44)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))&(r3_waybel_9(X44,X45,esk6_2(X44,X45))|~r2_hidden(X45,k6_yellow_6(X44))|(v2_struct_0(X45)|~v4_orders_2(X45)|~v7_waybel_0(X45)|~l1_waybel_0(X45,X44))|~v1_compts_1(X44)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(((((~v2_struct_0(esk7_1(X44))|v1_compts_1(X44)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))&(v4_orders_2(esk7_1(X44))|v1_compts_1(X44)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(v7_waybel_0(esk7_1(X44))|v1_compts_1(X44)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(l1_waybel_0(esk7_1(X44),X44)|v1_compts_1(X44)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&((r2_hidden(esk7_1(X44),k6_yellow_6(X44))|v1_compts_1(X44)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))&(~m1_subset_1(X48,u1_struct_0(X44))|~r3_waybel_9(X44,esk7_1(X44),X48)|v1_compts_1(X44)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_yellow19])])])])])])).
% 0.14/0.41  cnf(c_0_79, negated_conjecture, (k10_yellow_6(esk8_0,X1)=k1_xboole_0|r3_waybel_9(esk8_0,X2,esk2_3(esk8_0,X1,k1_xboole_0))|v2_struct_0(esk10_1(X2))|v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(esk2_3(esk8_0,X1,k1_xboole_0),k1_xboole_0)|k10_yellow_6(esk8_0,esk10_1(X2))!=k10_yellow_6(esk8_0,X1)|~l1_waybel_0(esk10_1(X2),esk8_0)|~l1_waybel_0(X2,esk8_0)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(esk10_1(X2))|~v7_waybel_0(X2)|~v7_waybel_0(X1)|~v4_orders_2(esk10_1(X2))|~v4_orders_2(X2)|~v4_orders_2(X1)|~m1_subset_1(esk2_3(esk8_0,X1,k1_xboole_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_38]), c_0_39])]), c_0_77]), c_0_40])).
% 0.14/0.41  cnf(c_0_80, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk7_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.14/0.41  cnf(c_0_81, negated_conjecture, (k10_yellow_6(esk8_0,esk10_1(X1))=k1_xboole_0|r3_waybel_9(esk8_0,X1,esk2_3(esk8_0,esk10_1(X1),k1_xboole_0))|v2_struct_0(esk10_1(X1))|v2_struct_0(X1)|r2_hidden(esk2_3(esk8_0,esk10_1(X1),k1_xboole_0),k1_xboole_0)|~l1_waybel_0(esk10_1(X1),esk8_0)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(esk10_1(X1))|~v7_waybel_0(X1)|~v4_orders_2(esk10_1(X1))|~v4_orders_2(X1)|~m1_subset_1(esk2_3(esk8_0,esk10_1(X1),k1_xboole_0),u1_struct_0(esk8_0))), inference(er,[status(thm)],[c_0_79])).
% 0.14/0.41  cnf(c_0_82, negated_conjecture, (k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0)))=k1_xboole_0|v2_struct_0(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))|r2_hidden(esk2_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),k1_xboole_0)|~l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)|~l1_waybel_0(esk7_1(esk8_0),esk8_0)|~v7_waybel_0(esk10_1(esk7_1(esk8_0)))|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk10_1(esk7_1(esk8_0)))|~v4_orders_2(esk7_1(esk8_0))|~m1_subset_1(esk2_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_38]), c_0_39])]), c_0_77]), c_0_40])).
% 0.14/0.41  cnf(c_0_83, negated_conjecture, (k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0)))=k1_xboole_0|v2_struct_0(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))|~l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)|~l1_waybel_0(esk7_1(esk8_0),esk8_0)|~v7_waybel_0(esk10_1(esk7_1(esk8_0)))|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk10_1(esk7_1(esk8_0)))|~v4_orders_2(esk7_1(esk8_0))|~m1_subset_1(esk2_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_82]), c_0_47])])).
% 0.14/0.41  cnf(c_0_84, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.41  cnf(c_0_85, negated_conjecture, (k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0)))=k1_xboole_0|v2_struct_0(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))|~l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)|~l1_waybel_0(esk7_1(esk8_0),esk8_0)|~v7_waybel_0(esk10_1(esk7_1(esk8_0)))|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk10_1(esk7_1(esk8_0)))|~v4_orders_2(esk7_1(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_36]), c_0_38]), c_0_39]), c_0_72])]), c_0_40])).
% 0.14/0.41  cnf(c_0_86, negated_conjecture, (v2_struct_0(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))|~v3_yellow_6(esk10_1(esk7_1(esk8_0)),esk8_0)|~l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)|~l1_waybel_0(esk7_1(esk8_0),esk8_0)|~v7_waybel_0(esk10_1(esk7_1(esk8_0)))|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk10_1(esk7_1(esk8_0)))|~v4_orders_2(esk7_1(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_38]), c_0_39])]), c_0_40])).
% 0.14/0.41  cnf(c_0_87, negated_conjecture, (v3_yellow_6(esk10_1(X1),esk8_0)|v2_struct_0(X1)|v1_compts_1(esk8_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_88, negated_conjecture, (v2_struct_0(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))|~l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)|~l1_waybel_0(esk7_1(esk8_0),esk8_0)|~v7_waybel_0(esk10_1(esk7_1(esk8_0)))|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk10_1(esk7_1(esk8_0)))|~v4_orders_2(esk7_1(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_77])).
% 0.14/0.41  cnf(c_0_89, negated_conjecture, (v1_compts_1(esk8_0)|l1_waybel_0(esk10_1(X1),esk8_0)|v2_struct_0(X1)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_62]), c_0_40])).
% 0.14/0.41  cnf(c_0_90, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(X1)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_struct_0(esk10_1(X1))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_62]), c_0_40])).
% 0.14/0.41  cnf(c_0_91, negated_conjecture, (v2_struct_0(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))|~l1_waybel_0(esk7_1(esk8_0),esk8_0)|~v7_waybel_0(esk10_1(esk7_1(esk8_0)))|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk10_1(esk7_1(esk8_0)))|~v4_orders_2(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_77])).
% 0.14/0.41  cnf(c_0_92, negated_conjecture, (v2_struct_0(esk7_1(esk8_0))|~l1_waybel_0(esk7_1(esk8_0),esk8_0)|~v7_waybel_0(esk10_1(esk7_1(esk8_0)))|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk10_1(esk7_1(esk8_0)))|~v4_orders_2(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_77])).
% 0.14/0.41  cnf(c_0_93, negated_conjecture, (v1_compts_1(esk8_0)|v7_waybel_0(esk10_1(X1))|v2_struct_0(X1)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_62]), c_0_40])).
% 0.14/0.41  cnf(c_0_94, negated_conjecture, (v2_struct_0(esk7_1(esk8_0))|~l1_waybel_0(esk7_1(esk8_0),esk8_0)|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk10_1(esk7_1(esk8_0)))|~v4_orders_2(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_77])).
% 0.14/0.41  cnf(c_0_95, negated_conjecture, (v1_compts_1(esk8_0)|v4_orders_2(esk10_1(X1))|v2_struct_0(X1)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_62]), c_0_40])).
% 0.14/0.41  cnf(c_0_96, negated_conjecture, (v2_struct_0(esk7_1(esk8_0))|~l1_waybel_0(esk7_1(esk8_0),esk8_0)|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_77])).
% 0.14/0.41  cnf(c_0_97, plain, (l1_waybel_0(esk7_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.14/0.41  cnf(c_0_98, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk7_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.14/0.41  cnf(c_0_99, negated_conjecture, (v2_struct_0(esk7_1(esk8_0))|~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_38]), c_0_39])]), c_0_77]), c_0_40])).
% 0.14/0.41  cnf(c_0_100, negated_conjecture, (~v7_waybel_0(esk7_1(esk8_0))|~v4_orders_2(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_38]), c_0_39])]), c_0_77]), c_0_40])).
% 0.14/0.41  cnf(c_0_101, plain, (v7_waybel_0(esk7_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.14/0.41  cnf(c_0_102, negated_conjecture, (~v4_orders_2(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_38]), c_0_39])]), c_0_77]), c_0_40])).
% 0.14/0.41  cnf(c_0_103, plain, (v4_orders_2(esk7_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.14/0.41  cnf(c_0_104, negated_conjecture, (~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_38]), c_0_39])]), c_0_77]), c_0_40])).
% 0.14/0.41  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_28]), c_0_39])]), ['proof']).
% 0.14/0.41  # SZS output end CNFRefutation
% 0.14/0.41  # Proof object total steps             : 106
% 0.14/0.41  # Proof object clause steps            : 75
% 0.14/0.41  # Proof object formula steps           : 31
% 0.14/0.41  # Proof object conjectures             : 39
% 0.14/0.41  # Proof object clause conjectures      : 36
% 0.14/0.41  # Proof object formula conjectures     : 3
% 0.14/0.41  # Proof object initial clauses used    : 37
% 0.14/0.41  # Proof object initial formulas used   : 15
% 0.14/0.41  # Proof object generating inferences   : 37
% 0.14/0.41  # Proof object simplifying inferences  : 105
% 0.14/0.41  # Training examples: 0 positive, 0 negative
% 0.14/0.41  # Parsed axioms                        : 15
% 0.14/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.41  # Initial clauses                      : 43
% 0.14/0.41  # Removed in clause preprocessing      : 0
% 0.14/0.41  # Initial clauses in saturation        : 43
% 0.14/0.41  # Processed clauses                    : 163
% 0.14/0.41  # ...of these trivial                  : 1
% 0.14/0.41  # ...subsumed                          : 16
% 0.14/0.41  # ...remaining for further processing  : 146
% 0.14/0.41  # Other redundant clauses eliminated   : 0
% 0.14/0.41  # Clauses deleted for lack of memory   : 0
% 0.14/0.41  # Backward-subsumed                    : 11
% 0.14/0.41  # Backward-rewritten                   : 0
% 0.14/0.41  # Generated clauses                    : 123
% 0.14/0.41  # ...of the previous two non-trivial   : 93
% 0.14/0.41  # Contextual simplify-reflections      : 85
% 0.14/0.41  # Paramodulations                      : 120
% 0.14/0.41  # Factorizations                       : 0
% 0.14/0.41  # Equation resolutions                 : 3
% 0.14/0.41  # Propositional unsat checks           : 0
% 0.14/0.41  #    Propositional check models        : 0
% 0.14/0.41  #    Propositional check unsatisfiable : 0
% 0.14/0.41  #    Propositional clauses             : 0
% 0.14/0.41  #    Propositional clauses after purity: 0
% 0.14/0.41  #    Propositional unsat core size     : 0
% 0.14/0.41  #    Propositional preprocessing time  : 0.000
% 0.14/0.41  #    Propositional encoding time       : 0.000
% 0.14/0.41  #    Propositional solver time         : 0.000
% 0.14/0.41  #    Success case prop preproc time    : 0.000
% 0.14/0.41  #    Success case prop encoding time   : 0.000
% 0.14/0.41  #    Success case prop solver time     : 0.000
% 0.14/0.41  # Current number of processed clauses  : 92
% 0.14/0.41  #    Positive orientable unit clauses  : 4
% 0.14/0.41  #    Positive unorientable unit clauses: 0
% 0.14/0.41  #    Negative unit clauses             : 3
% 0.14/0.41  #    Non-unit-clauses                  : 85
% 0.14/0.41  # Current number of unprocessed clauses: 12
% 0.14/0.41  # ...number of literals in the above   : 210
% 0.14/0.41  # Current number of archived formulas  : 0
% 0.14/0.41  # Current number of archived clauses   : 54
% 0.14/0.41  # Clause-clause subsumption calls (NU) : 15835
% 0.14/0.41  # Rec. Clause-clause subsumption calls : 226
% 0.14/0.41  # Non-unit clause-clause subsumptions  : 105
% 0.14/0.41  # Unit Clause-clause subsumption calls : 121
% 0.14/0.41  # Rewrite failures with RHS unbound    : 0
% 0.14/0.41  # BW rewrite match attempts            : 0
% 0.14/0.41  # BW rewrite match successes           : 0
% 0.14/0.41  # Condensation attempts                : 0
% 0.14/0.41  # Condensation successes               : 0
% 0.14/0.41  # Termbank termtop insertions          : 13419
% 0.14/0.41  
% 0.14/0.41  # -------------------------------------------------
% 0.14/0.41  # User time                : 0.060 s
% 0.14/0.41  # System time              : 0.006 s
% 0.14/0.41  # Total time               : 0.066 s
% 0.14/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
