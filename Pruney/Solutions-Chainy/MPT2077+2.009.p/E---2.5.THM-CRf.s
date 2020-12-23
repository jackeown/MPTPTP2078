%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:07 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  117 (2335 expanded)
%              Number of clauses        :   84 ( 759 expanded)
%              Number of leaves         :   16 ( 609 expanded)
%              Depth                    :   26
%              Number of atoms          : 1102 (27420 expanded)
%              Number of equality atoms :   39 ( 177 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal clause size      :   81 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(d9_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_waybel_9(X1,X2,X3)
              <=> ! [X4] :
                    ( m1_connsp_2(X4,X1,X3)
                   => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).

fof(t35_yellow19,axiom,(
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
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r3_waybel_9(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).

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

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_18,plain,
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

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | m1_subset_1(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_21,plain,(
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

cnf(c_0_22,plain,
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

cnf(c_0_23,plain,
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
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

fof(c_0_24,negated_conjecture,(
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

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | ~ r1_tarski(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_26,plain,(
    ! [X42,X43,X44] :
      ( ( m2_yellow_6(esk5_3(X42,X43,X44),X42,X43)
        | ~ r3_waybel_9(X42,X43,X44)
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | v2_struct_0(X43)
        | ~ v4_orders_2(X43)
        | ~ v7_waybel_0(X43)
        | ~ l1_waybel_0(X43,X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( r2_hidden(X44,k10_yellow_6(X42,esk5_3(X42,X43,X44)))
        | ~ r3_waybel_9(X42,X43,X44)
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | v2_struct_0(X43)
        | ~ v4_orders_2(X43)
        | ~ v7_waybel_0(X43)
        | ~ l1_waybel_0(X43,X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

fof(c_0_27,plain,(
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

fof(c_0_28,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_29,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | v2_struct_0(X40)
      | ~ v4_orders_2(X40)
      | ~ v7_waybel_0(X40)
      | ~ l1_waybel_0(X40,X39)
      | ~ m1_subset_1(X41,u1_struct_0(X39))
      | ~ r2_hidden(X41,k10_yellow_6(X39,X40))
      | r3_waybel_9(X39,X40,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
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
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19])).

fof(c_0_33,plain,(
    ! [X7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_34,negated_conjecture,(
    ! [X58,X59] :
      ( ~ v2_struct_0(esk10_0)
      & v2_pre_topc(esk10_0)
      & l1_pre_topc(esk10_0)
      & ( ~ v2_struct_0(esk11_0)
        | ~ v1_compts_1(esk10_0) )
      & ( v4_orders_2(esk11_0)
        | ~ v1_compts_1(esk10_0) )
      & ( v7_waybel_0(esk11_0)
        | ~ v1_compts_1(esk10_0) )
      & ( l1_waybel_0(esk11_0,esk10_0)
        | ~ v1_compts_1(esk10_0) )
      & ( ~ m2_yellow_6(X58,esk10_0,esk11_0)
        | ~ v3_yellow_6(X58,esk10_0)
        | ~ v1_compts_1(esk10_0) )
      & ( m2_yellow_6(esk12_1(X59),esk10_0,X59)
        | v2_struct_0(X59)
        | ~ v4_orders_2(X59)
        | ~ v7_waybel_0(X59)
        | ~ l1_waybel_0(X59,esk10_0)
        | v1_compts_1(esk10_0) )
      & ( v3_yellow_6(esk12_1(X59),esk10_0)
        | v2_struct_0(X59)
        | ~ v4_orders_2(X59)
        | ~ v7_waybel_0(X59)
        | ~ l1_waybel_0(X59,esk10_0)
        | v1_compts_1(esk10_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk5_3(X2,X3,X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_37,plain,(
    ! [X32,X33] :
      ( ( ~ v3_yellow_6(X33,X32)
        | k10_yellow_6(X32,X33) != k1_xboole_0
        | v2_struct_0(X33)
        | ~ v4_orders_2(X33)
        | ~ v7_waybel_0(X33)
        | ~ l1_waybel_0(X33,X32)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( k10_yellow_6(X32,X33) = k1_xboole_0
        | v3_yellow_6(X33,X32)
        | v2_struct_0(X33)
        | ~ v4_orders_2(X33)
        | ~ v7_waybel_0(X33)
        | ~ l1_waybel_0(X33,X32)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

fof(c_0_38,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_39,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( m2_yellow_6(esk5_3(X1,X2,X3),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_45,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ r3_waybel_9(X34,X35,X36)
        | ~ m1_connsp_2(X37,X34,X36)
        | r2_waybel_0(X34,X35,X37)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_connsp_2(esk4_3(X34,X35,X36),X34,X36)
        | r3_waybel_9(X34,X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ r2_waybel_0(X34,X35,esk4_3(X34,X35,X36))
        | r3_waybel_9(X34,X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,k10_yellow_6(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_48,plain,
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
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk10_0,esk11_0)
    | ~ v3_yellow_6(X1,esk10_0)
    | ~ v1_compts_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( v4_orders_2(esk11_0)
    | ~ v1_compts_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( v7_waybel_0(esk11_0)
    | ~ v1_compts_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_56,negated_conjecture,
    ( l1_waybel_0(esk11_0,esk10_0)
    | ~ v1_compts_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk11_0)
    | ~ v1_compts_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(k10_yellow_6(X1,esk5_3(X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_59,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_61,plain,
    ( v4_orders_2(esk5_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_62,plain,
    ( v7_waybel_0(esk5_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_41])).

cnf(c_0_63,plain,
    ( l1_waybel_0(esk5_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_41])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_struct_0(esk5_3(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_41])).

cnf(c_0_65,plain,
    ( r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_connsp_2(X4,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_66,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,k10_yellow_6(X1,X2)) ),
    inference(csr,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_67,plain,
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
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_49])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_compts_1(esk10_0)
    | ~ r3_waybel_9(esk10_0,esk11_0,X1)
    | ~ v3_yellow_6(esk5_3(esk10_0,esk11_0,X1),esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk10_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_40]),c_0_51]),c_0_52])]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_70,plain,
    ( v3_yellow_6(esk5_3(X1,X2,X3),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])]),c_0_61]),c_0_62]),c_0_63]),c_0_64])).

fof(c_0_71,plain,(
    ! [X46,X47,X50] :
      ( ( m1_subset_1(esk6_2(X46,X47),u1_struct_0(X46))
        | v2_struct_0(X47)
        | ~ v4_orders_2(X47)
        | ~ v7_waybel_0(X47)
        | ~ l1_waybel_0(X47,X46)
        | ~ v1_compts_1(X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( r3_waybel_9(X46,X47,esk6_2(X46,X47))
        | v2_struct_0(X47)
        | ~ v4_orders_2(X47)
        | ~ v7_waybel_0(X47)
        | ~ l1_waybel_0(X47,X46)
        | ~ v1_compts_1(X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ v2_struct_0(esk7_1(X46))
        | v1_compts_1(X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( v4_orders_2(esk7_1(X46))
        | v1_compts_1(X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( v7_waybel_0(esk7_1(X46))
        | v1_compts_1(X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( l1_waybel_0(esk7_1(X46),X46)
        | v1_compts_1(X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ m1_subset_1(X50,u1_struct_0(X46))
        | ~ r3_waybel_9(X46,esk7_1(X46),X50)
        | v1_compts_1(X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).

fof(c_0_72,plain,(
    ! [X28,X29,X30,X31] :
      ( v2_struct_0(X28)
      | ~ l1_struct_0(X28)
      | v2_struct_0(X29)
      | ~ v4_orders_2(X29)
      | ~ v7_waybel_0(X29)
      | ~ l1_waybel_0(X29,X28)
      | ~ m2_yellow_6(X30,X28,X29)
      | ~ r2_waybel_0(X28,X30,X31)
      | r2_waybel_0(X28,X29,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

cnf(c_0_73,plain,
    ( r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X1,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X4,k10_yellow_6(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_47])).

cnf(c_0_74,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | m1_subset_1(esk2_3(X1,X2,k1_xboole_0),u1_struct_0(X1))
    | k10_yellow_6(X1,X3) != k10_yellow_6(X1,X2)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X3)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_67]),c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_compts_1(esk10_0)
    | ~ r3_waybel_9(esk10_0,esk11_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk10_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_51]),c_0_52])]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_76,plain,
    ( r3_waybel_9(X1,X2,esk6_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( m2_yellow_6(esk12_1(X1),esk10_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk10_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_79,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | r2_waybel_0(X1,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | k10_yellow_6(X1,X3) != k10_yellow_6(X1,X2)
    | ~ m1_connsp_2(X4,X1,esk2_3(X1,X2,k1_xboole_0))
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X3)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_67])).

cnf(c_0_80,plain,
    ( m1_connsp_2(esk4_3(X1,X2,X3),X1,X3)
    | r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_81,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk2_3(X1,X2,k1_xboole_0),u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_compts_1(esk10_0)
    | ~ m1_subset_1(esk6_2(esk10_0,esk11_0),u1_struct_0(esk10_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_51]),c_0_52])]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_83,plain,
    ( m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( v1_compts_1(esk10_0)
    | r2_waybel_0(esk10_0,X1,X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(esk10_0,esk12_1(X1),X2)
    | ~ l1_waybel_0(X1,esk10_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_53])).

cnf(c_0_85,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | r3_waybel_9(X1,X3,esk2_3(X1,X2,k1_xboole_0))
    | r2_waybel_0(X1,X4,esk4_3(X1,X3,esk2_3(X1,X2,k1_xboole_0)))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | k10_yellow_6(X1,X4) != k10_yellow_6(X1,X2)
    | ~ l1_waybel_0(X4,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ v7_waybel_0(X4)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X4)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_compts_1(esk10_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_51]),c_0_52])]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_87,negated_conjecture,
    ( k10_yellow_6(esk10_0,X1) = k1_xboole_0
    | r3_waybel_9(esk10_0,X2,esk2_3(esk10_0,X1,k1_xboole_0))
    | r2_waybel_0(esk10_0,X3,esk4_3(esk10_0,X2,esk2_3(esk10_0,X1,k1_xboole_0)))
    | v2_struct_0(esk12_1(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_hidden(esk2_3(esk10_0,X1,k1_xboole_0),k1_xboole_0)
    | k10_yellow_6(esk10_0,esk12_1(X3)) != k10_yellow_6(esk10_0,X1)
    | ~ l1_waybel_0(esk12_1(X3),esk10_0)
    | ~ l1_waybel_0(X3,esk10_0)
    | ~ l1_waybel_0(X1,esk10_0)
    | ~ l1_waybel_0(X2,esk10_0)
    | ~ v7_waybel_0(esk12_1(X3))
    | ~ v7_waybel_0(X3)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk12_1(X3))
    | ~ v4_orders_2(X3)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_51]),c_0_52])]),c_0_86]),c_0_53])).

fof(c_0_88,plain,(
    ! [X51,X52,X55] :
      ( ( m1_subset_1(esk8_2(X51,X52),u1_struct_0(X51))
        | ~ r2_hidden(X52,k6_yellow_6(X51))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ v7_waybel_0(X52)
        | ~ l1_waybel_0(X52,X51)
        | ~ v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( r3_waybel_9(X51,X52,esk8_2(X51,X52))
        | ~ r2_hidden(X52,k6_yellow_6(X51))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ v7_waybel_0(X52)
        | ~ l1_waybel_0(X52,X51)
        | ~ v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( ~ v2_struct_0(esk9_1(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( v4_orders_2(esk9_1(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( v7_waybel_0(esk9_1(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( l1_waybel_0(esk9_1(X51),X51)
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( r2_hidden(esk9_1(X51),k6_yellow_6(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( ~ m1_subset_1(X55,u1_struct_0(X51))
        | ~ r3_waybel_9(X51,esk9_1(X51),X55)
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_yellow19])])])])])])).

cnf(c_0_89,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,esk4_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_90,negated_conjecture,
    ( k10_yellow_6(esk10_0,esk12_1(X1)) = k1_xboole_0
    | r3_waybel_9(esk10_0,X2,esk2_3(esk10_0,esk12_1(X1),k1_xboole_0))
    | r2_waybel_0(esk10_0,X1,esk4_3(esk10_0,X2,esk2_3(esk10_0,esk12_1(X1),k1_xboole_0)))
    | v2_struct_0(esk12_1(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(esk2_3(esk10_0,esk12_1(X1),k1_xboole_0),k1_xboole_0)
    | ~ l1_waybel_0(esk12_1(X1),esk10_0)
    | ~ l1_waybel_0(X1,esk10_0)
    | ~ l1_waybel_0(X2,esk10_0)
    | ~ v7_waybel_0(esk12_1(X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk12_1(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk10_0) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_91,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk9_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k10_yellow_6(esk10_0,esk12_1(X1)) = k1_xboole_0
    | r3_waybel_9(esk10_0,X1,esk2_3(esk10_0,esk12_1(X1),k1_xboole_0))
    | v2_struct_0(esk12_1(X1))
    | v2_struct_0(X1)
    | r2_hidden(esk2_3(esk10_0,esk12_1(X1),k1_xboole_0),k1_xboole_0)
    | ~ l1_waybel_0(esk12_1(X1),esk10_0)
    | ~ l1_waybel_0(X1,esk10_0)
    | ~ v7_waybel_0(esk12_1(X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk12_1(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk10_0)
    | ~ m1_subset_1(esk2_3(esk10_0,esk12_1(X1),k1_xboole_0),u1_struct_0(esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_93,negated_conjecture,
    ( k10_yellow_6(esk10_0,esk12_1(esk9_1(esk10_0))) = k1_xboole_0
    | v2_struct_0(esk12_1(esk9_1(esk10_0)))
    | v2_struct_0(esk9_1(esk10_0))
    | r2_hidden(esk2_3(esk10_0,esk12_1(esk9_1(esk10_0)),k1_xboole_0),k1_xboole_0)
    | ~ l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)
    | ~ l1_waybel_0(esk9_1(esk10_0),esk10_0)
    | ~ v7_waybel_0(esk12_1(esk9_1(esk10_0)))
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk12_1(esk9_1(esk10_0)))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0)
    | ~ m1_subset_1(esk2_3(esk10_0,esk12_1(esk9_1(esk10_0)),k1_xboole_0),u1_struct_0(esk10_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_51]),c_0_52])]),c_0_86]),c_0_53])).

cnf(c_0_94,negated_conjecture,
    ( k10_yellow_6(esk10_0,esk12_1(esk9_1(esk10_0))) = k1_xboole_0
    | v2_struct_0(esk12_1(esk9_1(esk10_0)))
    | v2_struct_0(esk9_1(esk10_0))
    | ~ l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)
    | ~ l1_waybel_0(esk9_1(esk10_0),esk10_0)
    | ~ v7_waybel_0(esk12_1(esk9_1(esk10_0)))
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk12_1(esk9_1(esk10_0)))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0)
    | ~ m1_subset_1(esk2_3(esk10_0,esk12_1(esk9_1(esk10_0)),k1_xboole_0),u1_struct_0(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_93]),c_0_60])])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_96,negated_conjecture,
    ( k10_yellow_6(esk10_0,esk12_1(esk9_1(esk10_0))) = k1_xboole_0
    | v2_struct_0(esk12_1(esk9_1(esk10_0)))
    | v2_struct_0(esk9_1(esk10_0))
    | ~ l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)
    | ~ l1_waybel_0(esk9_1(esk10_0),esk10_0)
    | ~ v7_waybel_0(esk12_1(esk9_1(esk10_0)))
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk12_1(esk9_1(esk10_0)))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_19]),c_0_51]),c_0_52]),c_0_49])]),c_0_53])).

cnf(c_0_97,negated_conjecture,
    ( v2_struct_0(esk12_1(esk9_1(esk10_0)))
    | v2_struct_0(esk9_1(esk10_0))
    | ~ v3_yellow_6(esk12_1(esk9_1(esk10_0)),esk10_0)
    | ~ l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)
    | ~ l1_waybel_0(esk9_1(esk10_0),esk10_0)
    | ~ v7_waybel_0(esk12_1(esk9_1(esk10_0)))
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk12_1(esk9_1(esk10_0)))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_98,negated_conjecture,
    ( v3_yellow_6(esk12_1(X1),esk10_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk10_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_99,negated_conjecture,
    ( v2_struct_0(esk12_1(esk9_1(esk10_0)))
    | v2_struct_0(esk9_1(esk10_0))
    | ~ l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)
    | ~ l1_waybel_0(esk9_1(esk10_0),esk10_0)
    | ~ v7_waybel_0(esk12_1(esk9_1(esk10_0)))
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk12_1(esk9_1(esk10_0)))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_86])).

cnf(c_0_100,negated_conjecture,
    ( v1_compts_1(esk10_0)
    | l1_waybel_0(esk12_1(X1),esk10_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk10_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_78]),c_0_53])).

cnf(c_0_101,negated_conjecture,
    ( v1_compts_1(esk10_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk10_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_struct_0(esk12_1(X1))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_78]),c_0_53])).

cnf(c_0_102,negated_conjecture,
    ( v2_struct_0(esk12_1(esk9_1(esk10_0)))
    | v2_struct_0(esk9_1(esk10_0))
    | ~ l1_waybel_0(esk9_1(esk10_0),esk10_0)
    | ~ v7_waybel_0(esk12_1(esk9_1(esk10_0)))
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk12_1(esk9_1(esk10_0)))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_86])).

cnf(c_0_103,negated_conjecture,
    ( v2_struct_0(esk9_1(esk10_0))
    | ~ l1_waybel_0(esk9_1(esk10_0),esk10_0)
    | ~ v7_waybel_0(esk12_1(esk9_1(esk10_0)))
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk12_1(esk9_1(esk10_0)))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_86])).

cnf(c_0_104,negated_conjecture,
    ( v1_compts_1(esk10_0)
    | v7_waybel_0(esk12_1(X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk10_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_78]),c_0_53])).

cnf(c_0_105,negated_conjecture,
    ( v2_struct_0(esk9_1(esk10_0))
    | ~ l1_waybel_0(esk9_1(esk10_0),esk10_0)
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk12_1(esk9_1(esk10_0)))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_86])).

cnf(c_0_106,negated_conjecture,
    ( v1_compts_1(esk10_0)
    | v4_orders_2(esk12_1(X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk10_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_78]),c_0_53])).

cnf(c_0_107,negated_conjecture,
    ( v2_struct_0(esk9_1(esk10_0))
    | ~ l1_waybel_0(esk9_1(esk10_0),esk10_0)
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_86])).

cnf(c_0_108,plain,
    ( l1_waybel_0(esk9_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_109,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk9_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_110,negated_conjecture,
    ( v2_struct_0(esk9_1(esk10_0))
    | ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_51]),c_0_52])]),c_0_86]),c_0_53])).

cnf(c_0_111,negated_conjecture,
    ( ~ v7_waybel_0(esk9_1(esk10_0))
    | ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_51]),c_0_52])]),c_0_86]),c_0_53])).

cnf(c_0_112,plain,
    ( v7_waybel_0(esk9_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_113,negated_conjecture,
    ( ~ v4_orders_2(esk9_1(esk10_0))
    | ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_51]),c_0_52])]),c_0_86]),c_0_53])).

cnf(c_0_114,plain,
    ( v4_orders_2(esk9_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_115,negated_conjecture,
    ( ~ l1_struct_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_51]),c_0_52])]),c_0_86]),c_0_53])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_41]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:50:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.78/0.94  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.78/0.94  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.78/0.94  #
% 0.78/0.94  # Preprocessing time       : 0.031 s
% 0.78/0.94  # Presaturation interreduction done
% 0.78/0.94  
% 0.78/0.94  # Proof found!
% 0.78/0.94  # SZS status Theorem
% 0.78/0.94  # SZS output start CNFRefutation
% 0.78/0.94  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.78/0.94  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.78/0.94  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.78/0.94  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 0.78/0.94  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.78/0.94  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.78/0.94  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.78/0.94  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.78/0.94  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.78/0.94  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.78/0.94  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.78/0.94  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.78/0.94  fof(d9_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>![X4]:(m1_connsp_2(X4,X1,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_waybel_9)).
% 0.78/0.94  fof(t35_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_yellow19)).
% 0.78/0.94  fof(t27_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(r2_waybel_0(X1,X3,X4)=>r2_waybel_0(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_6)).
% 0.78/0.94  fof(t36_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>~((r2_hidden(X2,k6_yellow_6(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r3_waybel_9(X1,X2,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_yellow19)).
% 0.78/0.94  fof(c_0_16, plain, ![X14, X15, X16, X17, X18, X22]:(((~r2_hidden(X17,X16)|(~m1_connsp_2(X18,X14,X17)|r1_waybel_0(X14,X15,X18))|~m1_subset_1(X17,u1_struct_0(X14))|X16!=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&((m1_connsp_2(esk1_4(X14,X15,X16,X17),X14,X17)|r2_hidden(X17,X16)|~m1_subset_1(X17,u1_struct_0(X14))|X16!=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r1_waybel_0(X14,X15,esk1_4(X14,X15,X16,X17))|r2_hidden(X17,X16)|~m1_subset_1(X17,u1_struct_0(X14))|X16!=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))))&((m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(((m1_connsp_2(esk3_3(X14,X15,X16),X14,esk2_3(X14,X15,X16))|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r1_waybel_0(X14,X15,esk3_3(X14,X15,X16))|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))))&(r2_hidden(esk2_3(X14,X15,X16),X16)|(~m1_connsp_2(X22,X14,esk2_3(X14,X15,X16))|r1_waybel_0(X14,X15,X22))|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.78/0.94  cnf(c_0_17, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r1_waybel_0(X1,X2,X4)|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X4,X1,esk2_3(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.94  cnf(c_0_18, plain, (m1_connsp_2(esk1_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.94  cnf(c_0_19, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.94  fof(c_0_20, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|m1_subset_1(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.78/0.94  fof(c_0_21, plain, ![X23, X24]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23)|m1_subset_1(k10_yellow_6(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.78/0.94  cnf(c_0_22, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk1_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.94  cnf(c_0_23, plain, (X1=k10_yellow_6(X2,X3)|r1_waybel_0(X2,X3,esk1_4(X2,X4,X5,esk2_3(X2,X3,X1)))|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk2_3(X2,X3,X1),X5)|r2_hidden(esk2_3(X2,X3,X1),X1)|X5!=k10_yellow_6(X2,X4)|~l1_waybel_0(X3,X2)|~l1_waybel_0(X4,X2)|~v7_waybel_0(X3)|~v7_waybel_0(X4)|~v4_orders_2(X3)|~v4_orders_2(X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.78/0.94  fof(c_0_24, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.78/0.94  fof(c_0_25, plain, ![X11, X12]:(~r2_hidden(X11,X12)|~r1_tarski(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.78/0.94  fof(c_0_26, plain, ![X42, X43, X44]:((m2_yellow_6(esk5_3(X42,X43,X44),X42,X43)|~r3_waybel_9(X42,X43,X44)|~m1_subset_1(X44,u1_struct_0(X42))|(v2_struct_0(X43)|~v4_orders_2(X43)|~v7_waybel_0(X43)|~l1_waybel_0(X43,X42))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))&(r2_hidden(X44,k10_yellow_6(X42,esk5_3(X42,X43,X44)))|~r3_waybel_9(X42,X43,X44)|~m1_subset_1(X44,u1_struct_0(X42))|(v2_struct_0(X43)|~v4_orders_2(X43)|~v7_waybel_0(X43)|~l1_waybel_0(X43,X42))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.78/0.94  fof(c_0_27, plain, ![X25, X26, X27]:((((~v2_struct_0(X27)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25)))&(v4_orders_2(X27)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))))&(v7_waybel_0(X27)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))))&(l1_waybel_0(X27,X25)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.78/0.94  fof(c_0_28, plain, ![X13]:(~l1_pre_topc(X13)|l1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.78/0.94  fof(c_0_29, plain, ![X39, X40, X41]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(v2_struct_0(X40)|~v4_orders_2(X40)|~v7_waybel_0(X40)|~l1_waybel_0(X40,X39)|(~m1_subset_1(X41,u1_struct_0(X39))|(~r2_hidden(X41,k10_yellow_6(X39,X40))|r3_waybel_9(X39,X40,X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.78/0.94  cnf(c_0_30, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.78/0.94  cnf(c_0_31, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.78/0.94  cnf(c_0_32, plain, (X1=k10_yellow_6(X2,X3)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|r2_hidden(esk2_3(X2,X3,X1),X4)|X4!=k10_yellow_6(X2,X3)|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_19])).
% 0.78/0.94  fof(c_0_33, plain, ![X7]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.78/0.94  fof(c_0_34, negated_conjecture, ![X58, X59]:(((~v2_struct_0(esk10_0)&v2_pre_topc(esk10_0))&l1_pre_topc(esk10_0))&((((((~v2_struct_0(esk11_0)|~v1_compts_1(esk10_0))&(v4_orders_2(esk11_0)|~v1_compts_1(esk10_0)))&(v7_waybel_0(esk11_0)|~v1_compts_1(esk10_0)))&(l1_waybel_0(esk11_0,esk10_0)|~v1_compts_1(esk10_0)))&(~m2_yellow_6(X58,esk10_0,esk11_0)|~v3_yellow_6(X58,esk10_0)|~v1_compts_1(esk10_0)))&((m2_yellow_6(esk12_1(X59),esk10_0,X59)|(v2_struct_0(X59)|~v4_orders_2(X59)|~v7_waybel_0(X59)|~l1_waybel_0(X59,esk10_0))|v1_compts_1(esk10_0))&(v3_yellow_6(esk12_1(X59),esk10_0)|(v2_struct_0(X59)|~v4_orders_2(X59)|~v7_waybel_0(X59)|~l1_waybel_0(X59,esk10_0))|v1_compts_1(esk10_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])])])).
% 0.78/0.94  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.78/0.94  cnf(c_0_36, plain, (r2_hidden(X1,k10_yellow_6(X2,esk5_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.78/0.94  fof(c_0_37, plain, ![X32, X33]:((~v3_yellow_6(X33,X32)|k10_yellow_6(X32,X33)!=k1_xboole_0|(v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(k10_yellow_6(X32,X33)=k1_xboole_0|v3_yellow_6(X33,X32)|(v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.78/0.94  fof(c_0_38, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.78/0.94  cnf(c_0_39, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.78/0.94  cnf(c_0_40, plain, (m2_yellow_6(esk5_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.78/0.94  cnf(c_0_41, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.78/0.94  cnf(c_0_42, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.78/0.94  cnf(c_0_43, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.78/0.94  cnf(c_0_44, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.78/0.94  fof(c_0_45, plain, ![X34, X35, X36, X37]:((~r3_waybel_9(X34,X35,X36)|(~m1_connsp_2(X37,X34,X36)|r2_waybel_0(X34,X35,X37))|~m1_subset_1(X36,u1_struct_0(X34))|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&((m1_connsp_2(esk4_3(X34,X35,X36),X34,X36)|r3_waybel_9(X34,X35,X36)|~m1_subset_1(X36,u1_struct_0(X34))|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(~r2_waybel_0(X34,X35,esk4_3(X34,X35,X36))|r3_waybel_9(X34,X35,X36)|~m1_subset_1(X36,u1_struct_0(X34))|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).
% 0.78/0.94  cnf(c_0_46, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.78/0.94  cnf(c_0_47, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.78/0.94  cnf(c_0_48, plain, (X1=k10_yellow_6(X2,X3)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|r2_hidden(esk2_3(X2,X3,X1),k10_yellow_6(X2,X4))|r2_hidden(esk2_3(X2,X3,X1),X1)|k10_yellow_6(X2,X4)!=k10_yellow_6(X2,X3)|~l1_waybel_0(X3,X2)|~l1_waybel_0(X4,X2)|~v7_waybel_0(X3)|~v7_waybel_0(X4)|~v4_orders_2(X3)|~v4_orders_2(X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.78/0.94  cnf(c_0_49, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.78/0.94  cnf(c_0_50, negated_conjecture, (~m2_yellow_6(X1,esk10_0,esk11_0)|~v3_yellow_6(X1,esk10_0)|~v1_compts_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_54, negated_conjecture, (v4_orders_2(esk11_0)|~v1_compts_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_55, negated_conjecture, (v7_waybel_0(esk11_0)|~v1_compts_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_56, negated_conjecture, (l1_waybel_0(esk11_0,esk10_0)|~v1_compts_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_57, negated_conjecture, (~v2_struct_0(esk11_0)|~v1_compts_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_58, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(k10_yellow_6(X1,esk5_3(X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.78/0.94  cnf(c_0_59, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.78/0.94  cnf(c_0_60, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.78/0.94  cnf(c_0_61, plain, (v4_orders_2(esk5_3(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.78/0.94  cnf(c_0_62, plain, (v7_waybel_0(esk5_3(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_40]), c_0_41])).
% 0.78/0.94  cnf(c_0_63, plain, (l1_waybel_0(esk5_3(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_41])).
% 0.78/0.94  cnf(c_0_64, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~v2_struct_0(esk5_3(X1,X2,X3))|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_41])).
% 0.78/0.94  cnf(c_0_65, plain, (r2_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_connsp_2(X4,X1,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.78/0.94  cnf(c_0_66, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(csr,[status(thm)],[c_0_46, c_0_47])).
% 0.78/0.94  cnf(c_0_67, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk2_3(X1,X2,k1_xboole_0),k10_yellow_6(X1,X3))|r2_hidden(esk2_3(X1,X2,k1_xboole_0),k1_xboole_0)|k10_yellow_6(X1,X3)!=k10_yellow_6(X1,X2)|~l1_waybel_0(X2,X1)|~l1_waybel_0(X3,X1)|~v7_waybel_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X2)|~v4_orders_2(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.78/0.94  cnf(c_0_68, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_49])).
% 0.78/0.94  cnf(c_0_69, negated_conjecture, (~v1_compts_1(esk10_0)|~r3_waybel_9(esk10_0,esk11_0,X1)|~v3_yellow_6(esk5_3(esk10_0,esk11_0,X1),esk10_0)|~m1_subset_1(X1,u1_struct_0(esk10_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_40]), c_0_51]), c_0_52])]), c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57])).
% 0.78/0.94  cnf(c_0_70, plain, (v3_yellow_6(esk5_3(X1,X2,X3),X1)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])]), c_0_61]), c_0_62]), c_0_63]), c_0_64])).
% 0.78/0.94  fof(c_0_71, plain, ![X46, X47, X50]:(((m1_subset_1(esk6_2(X46,X47),u1_struct_0(X46))|(v2_struct_0(X47)|~v4_orders_2(X47)|~v7_waybel_0(X47)|~l1_waybel_0(X47,X46))|~v1_compts_1(X46)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(r3_waybel_9(X46,X47,esk6_2(X46,X47))|(v2_struct_0(X47)|~v4_orders_2(X47)|~v7_waybel_0(X47)|~l1_waybel_0(X47,X46))|~v1_compts_1(X46)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))))&(((((~v2_struct_0(esk7_1(X46))|v1_compts_1(X46)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(v4_orders_2(esk7_1(X46))|v1_compts_1(X46)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))))&(v7_waybel_0(esk7_1(X46))|v1_compts_1(X46)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))))&(l1_waybel_0(esk7_1(X46),X46)|v1_compts_1(X46)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))))&(~m1_subset_1(X50,u1_struct_0(X46))|~r3_waybel_9(X46,esk7_1(X46),X50)|v1_compts_1(X46)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).
% 0.78/0.94  fof(c_0_72, plain, ![X28, X29, X30, X31]:(v2_struct_0(X28)|~l1_struct_0(X28)|(v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28)|(~m2_yellow_6(X30,X28,X29)|(~r2_waybel_0(X28,X30,X31)|r2_waybel_0(X28,X29,X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).
% 0.78/0.94  cnf(c_0_73, plain, (r2_waybel_0(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_connsp_2(X3,X1,X4)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X4,k10_yellow_6(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_47])).
% 0.78/0.94  cnf(c_0_74, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X1)|m1_subset_1(esk2_3(X1,X2,k1_xboole_0),u1_struct_0(X1))|k10_yellow_6(X1,X3)!=k10_yellow_6(X1,X2)|~l1_waybel_0(X3,X1)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X3)|~v7_waybel_0(X2)|~v4_orders_2(X3)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_67]), c_0_68])).
% 0.78/0.94  cnf(c_0_75, negated_conjecture, (~v1_compts_1(esk10_0)|~r3_waybel_9(esk10_0,esk11_0,X1)|~m1_subset_1(X1,u1_struct_0(esk10_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_51]), c_0_52])]), c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57])).
% 0.78/0.94  cnf(c_0_76, plain, (r3_waybel_9(X1,X2,esk6_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.78/0.94  cnf(c_0_77, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_waybel_0(X1,X2,X4)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~r2_waybel_0(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.78/0.94  cnf(c_0_78, negated_conjecture, (m2_yellow_6(esk12_1(X1),esk10_0,X1)|v2_struct_0(X1)|v1_compts_1(esk10_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_79, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|r2_waybel_0(X1,X3,X4)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X1)|r2_hidden(esk2_3(X1,X2,k1_xboole_0),k1_xboole_0)|k10_yellow_6(X1,X3)!=k10_yellow_6(X1,X2)|~m1_connsp_2(X4,X1,esk2_3(X1,X2,k1_xboole_0))|~l1_waybel_0(X3,X1)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X3)|~v7_waybel_0(X2)|~v4_orders_2(X3)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_73, c_0_67])).
% 0.78/0.94  cnf(c_0_80, plain, (m1_connsp_2(esk4_3(X1,X2,X3),X1,X3)|r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.78/0.94  cnf(c_0_81, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk2_3(X1,X2,k1_xboole_0),u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_74])).
% 0.78/0.94  cnf(c_0_82, negated_conjecture, (~v1_compts_1(esk10_0)|~m1_subset_1(esk6_2(esk10_0,esk11_0),u1_struct_0(esk10_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_51]), c_0_52])]), c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57])).
% 0.78/0.94  cnf(c_0_83, plain, (m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.78/0.94  cnf(c_0_84, negated_conjecture, (v1_compts_1(esk10_0)|r2_waybel_0(esk10_0,X1,X2)|v2_struct_0(X1)|~r2_waybel_0(esk10_0,esk12_1(X1),X2)|~l1_waybel_0(X1,esk10_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_53])).
% 0.78/0.94  cnf(c_0_85, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|r3_waybel_9(X1,X3,esk2_3(X1,X2,k1_xboole_0))|r2_waybel_0(X1,X4,esk4_3(X1,X3,esk2_3(X1,X2,k1_xboole_0)))|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|r2_hidden(esk2_3(X1,X2,k1_xboole_0),k1_xboole_0)|k10_yellow_6(X1,X4)!=k10_yellow_6(X1,X2)|~l1_waybel_0(X4,X1)|~l1_waybel_0(X2,X1)|~l1_waybel_0(X3,X1)|~v7_waybel_0(X4)|~v7_waybel_0(X2)|~v4_orders_2(X4)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.78/0.94  cnf(c_0_86, negated_conjecture, (~v1_compts_1(esk10_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_51]), c_0_52])]), c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57])).
% 0.78/0.94  cnf(c_0_87, negated_conjecture, (k10_yellow_6(esk10_0,X1)=k1_xboole_0|r3_waybel_9(esk10_0,X2,esk2_3(esk10_0,X1,k1_xboole_0))|r2_waybel_0(esk10_0,X3,esk4_3(esk10_0,X2,esk2_3(esk10_0,X1,k1_xboole_0)))|v2_struct_0(esk12_1(X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk2_3(esk10_0,X1,k1_xboole_0),k1_xboole_0)|k10_yellow_6(esk10_0,esk12_1(X3))!=k10_yellow_6(esk10_0,X1)|~l1_waybel_0(esk12_1(X3),esk10_0)|~l1_waybel_0(X3,esk10_0)|~l1_waybel_0(X1,esk10_0)|~l1_waybel_0(X2,esk10_0)|~v7_waybel_0(esk12_1(X3))|~v7_waybel_0(X3)|~v7_waybel_0(X1)|~v4_orders_2(esk12_1(X3))|~v4_orders_2(X3)|~v4_orders_2(X1)|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_51]), c_0_52])]), c_0_86]), c_0_53])).
% 0.78/0.94  fof(c_0_88, plain, ![X51, X52, X55]:(((m1_subset_1(esk8_2(X51,X52),u1_struct_0(X51))|~r2_hidden(X52,k6_yellow_6(X51))|(v2_struct_0(X52)|~v4_orders_2(X52)|~v7_waybel_0(X52)|~l1_waybel_0(X52,X51))|~v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)))&(r3_waybel_9(X51,X52,esk8_2(X51,X52))|~r2_hidden(X52,k6_yellow_6(X51))|(v2_struct_0(X52)|~v4_orders_2(X52)|~v7_waybel_0(X52)|~l1_waybel_0(X52,X51))|~v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))))&(((((~v2_struct_0(esk9_1(X51))|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)))&(v4_orders_2(esk9_1(X51))|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))))&(v7_waybel_0(esk9_1(X51))|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))))&(l1_waybel_0(esk9_1(X51),X51)|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))))&((r2_hidden(esk9_1(X51),k6_yellow_6(X51))|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)))&(~m1_subset_1(X55,u1_struct_0(X51))|~r3_waybel_9(X51,esk9_1(X51),X55)|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_yellow19])])])])])])).
% 0.78/0.94  cnf(c_0_89, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_0(X1,X2,esk4_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.78/0.94  cnf(c_0_90, negated_conjecture, (k10_yellow_6(esk10_0,esk12_1(X1))=k1_xboole_0|r3_waybel_9(esk10_0,X2,esk2_3(esk10_0,esk12_1(X1),k1_xboole_0))|r2_waybel_0(esk10_0,X1,esk4_3(esk10_0,X2,esk2_3(esk10_0,esk12_1(X1),k1_xboole_0)))|v2_struct_0(esk12_1(X1))|v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(esk2_3(esk10_0,esk12_1(X1),k1_xboole_0),k1_xboole_0)|~l1_waybel_0(esk12_1(X1),esk10_0)|~l1_waybel_0(X1,esk10_0)|~l1_waybel_0(X2,esk10_0)|~v7_waybel_0(esk12_1(X1))|~v7_waybel_0(X1)|~v4_orders_2(esk12_1(X1))|~v4_orders_2(X1)|~l1_struct_0(esk10_0)), inference(er,[status(thm)],[c_0_87])).
% 0.78/0.94  cnf(c_0_91, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk9_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.78/0.94  cnf(c_0_92, negated_conjecture, (k10_yellow_6(esk10_0,esk12_1(X1))=k1_xboole_0|r3_waybel_9(esk10_0,X1,esk2_3(esk10_0,esk12_1(X1),k1_xboole_0))|v2_struct_0(esk12_1(X1))|v2_struct_0(X1)|r2_hidden(esk2_3(esk10_0,esk12_1(X1),k1_xboole_0),k1_xboole_0)|~l1_waybel_0(esk12_1(X1),esk10_0)|~l1_waybel_0(X1,esk10_0)|~v7_waybel_0(esk12_1(X1))|~v7_waybel_0(X1)|~v4_orders_2(esk12_1(X1))|~v4_orders_2(X1)|~l1_struct_0(esk10_0)|~m1_subset_1(esk2_3(esk10_0,esk12_1(X1),k1_xboole_0),u1_struct_0(esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_51]), c_0_52])]), c_0_53])).
% 0.78/0.94  cnf(c_0_93, negated_conjecture, (k10_yellow_6(esk10_0,esk12_1(esk9_1(esk10_0)))=k1_xboole_0|v2_struct_0(esk12_1(esk9_1(esk10_0)))|v2_struct_0(esk9_1(esk10_0))|r2_hidden(esk2_3(esk10_0,esk12_1(esk9_1(esk10_0)),k1_xboole_0),k1_xboole_0)|~l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)|~l1_waybel_0(esk9_1(esk10_0),esk10_0)|~v7_waybel_0(esk12_1(esk9_1(esk10_0)))|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk12_1(esk9_1(esk10_0)))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)|~m1_subset_1(esk2_3(esk10_0,esk12_1(esk9_1(esk10_0)),k1_xboole_0),u1_struct_0(esk10_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_51]), c_0_52])]), c_0_86]), c_0_53])).
% 0.78/0.94  cnf(c_0_94, negated_conjecture, (k10_yellow_6(esk10_0,esk12_1(esk9_1(esk10_0)))=k1_xboole_0|v2_struct_0(esk12_1(esk9_1(esk10_0)))|v2_struct_0(esk9_1(esk10_0))|~l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)|~l1_waybel_0(esk9_1(esk10_0),esk10_0)|~v7_waybel_0(esk12_1(esk9_1(esk10_0)))|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk12_1(esk9_1(esk10_0)))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)|~m1_subset_1(esk2_3(esk10_0,esk12_1(esk9_1(esk10_0)),k1_xboole_0),u1_struct_0(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_93]), c_0_60])])).
% 0.78/0.94  cnf(c_0_95, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.78/0.94  cnf(c_0_96, negated_conjecture, (k10_yellow_6(esk10_0,esk12_1(esk9_1(esk10_0)))=k1_xboole_0|v2_struct_0(esk12_1(esk9_1(esk10_0)))|v2_struct_0(esk9_1(esk10_0))|~l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)|~l1_waybel_0(esk9_1(esk10_0),esk10_0)|~v7_waybel_0(esk12_1(esk9_1(esk10_0)))|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk12_1(esk9_1(esk10_0)))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_19]), c_0_51]), c_0_52]), c_0_49])]), c_0_53])).
% 0.78/0.94  cnf(c_0_97, negated_conjecture, (v2_struct_0(esk12_1(esk9_1(esk10_0)))|v2_struct_0(esk9_1(esk10_0))|~v3_yellow_6(esk12_1(esk9_1(esk10_0)),esk10_0)|~l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)|~l1_waybel_0(esk9_1(esk10_0),esk10_0)|~v7_waybel_0(esk12_1(esk9_1(esk10_0)))|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk12_1(esk9_1(esk10_0)))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_51]), c_0_52])]), c_0_53])).
% 0.78/0.94  cnf(c_0_98, negated_conjecture, (v3_yellow_6(esk12_1(X1),esk10_0)|v2_struct_0(X1)|v1_compts_1(esk10_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.94  cnf(c_0_99, negated_conjecture, (v2_struct_0(esk12_1(esk9_1(esk10_0)))|v2_struct_0(esk9_1(esk10_0))|~l1_waybel_0(esk12_1(esk9_1(esk10_0)),esk10_0)|~l1_waybel_0(esk9_1(esk10_0),esk10_0)|~v7_waybel_0(esk12_1(esk9_1(esk10_0)))|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk12_1(esk9_1(esk10_0)))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_86])).
% 0.78/0.94  cnf(c_0_100, negated_conjecture, (v1_compts_1(esk10_0)|l1_waybel_0(esk12_1(X1),esk10_0)|v2_struct_0(X1)|~l1_waybel_0(X1,esk10_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_78]), c_0_53])).
% 0.78/0.94  cnf(c_0_101, negated_conjecture, (v1_compts_1(esk10_0)|v2_struct_0(X1)|~l1_waybel_0(X1,esk10_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_struct_0(esk12_1(X1))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_78]), c_0_53])).
% 0.78/0.94  cnf(c_0_102, negated_conjecture, (v2_struct_0(esk12_1(esk9_1(esk10_0)))|v2_struct_0(esk9_1(esk10_0))|~l1_waybel_0(esk9_1(esk10_0),esk10_0)|~v7_waybel_0(esk12_1(esk9_1(esk10_0)))|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk12_1(esk9_1(esk10_0)))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_86])).
% 0.78/0.94  cnf(c_0_103, negated_conjecture, (v2_struct_0(esk9_1(esk10_0))|~l1_waybel_0(esk9_1(esk10_0),esk10_0)|~v7_waybel_0(esk12_1(esk9_1(esk10_0)))|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk12_1(esk9_1(esk10_0)))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_86])).
% 0.78/0.94  cnf(c_0_104, negated_conjecture, (v1_compts_1(esk10_0)|v7_waybel_0(esk12_1(X1))|v2_struct_0(X1)|~l1_waybel_0(X1,esk10_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_78]), c_0_53])).
% 0.78/0.94  cnf(c_0_105, negated_conjecture, (v2_struct_0(esk9_1(esk10_0))|~l1_waybel_0(esk9_1(esk10_0),esk10_0)|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk12_1(esk9_1(esk10_0)))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_86])).
% 0.78/0.94  cnf(c_0_106, negated_conjecture, (v1_compts_1(esk10_0)|v4_orders_2(esk12_1(X1))|v2_struct_0(X1)|~l1_waybel_0(X1,esk10_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_78]), c_0_53])).
% 0.78/0.94  cnf(c_0_107, negated_conjecture, (v2_struct_0(esk9_1(esk10_0))|~l1_waybel_0(esk9_1(esk10_0),esk10_0)|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_86])).
% 0.78/0.94  cnf(c_0_108, plain, (l1_waybel_0(esk9_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.78/0.94  cnf(c_0_109, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk9_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.78/0.94  cnf(c_0_110, negated_conjecture, (v2_struct_0(esk9_1(esk10_0))|~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_51]), c_0_52])]), c_0_86]), c_0_53])).
% 0.78/0.94  cnf(c_0_111, negated_conjecture, (~v7_waybel_0(esk9_1(esk10_0))|~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_51]), c_0_52])]), c_0_86]), c_0_53])).
% 0.78/0.94  cnf(c_0_112, plain, (v7_waybel_0(esk9_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.78/0.94  cnf(c_0_113, negated_conjecture, (~v4_orders_2(esk9_1(esk10_0))|~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_51]), c_0_52])]), c_0_86]), c_0_53])).
% 0.78/0.94  cnf(c_0_114, plain, (v4_orders_2(esk9_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.78/0.94  cnf(c_0_115, negated_conjecture, (~l1_struct_0(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_51]), c_0_52])]), c_0_86]), c_0_53])).
% 0.78/0.94  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_41]), c_0_52])]), ['proof']).
% 0.78/0.94  # SZS output end CNFRefutation
% 0.78/0.94  # Proof object total steps             : 117
% 0.78/0.94  # Proof object clause steps            : 84
% 0.78/0.94  # Proof object formula steps           : 33
% 0.78/0.94  # Proof object conjectures             : 39
% 0.78/0.94  # Proof object clause conjectures      : 36
% 0.78/0.94  # Proof object formula conjectures     : 3
% 0.78/0.94  # Proof object initial clauses used    : 40
% 0.78/0.94  # Proof object initial formulas used   : 16
% 0.78/0.94  # Proof object generating inferences   : 43
% 0.78/0.94  # Proof object simplifying inferences  : 105
% 0.78/0.94  # Training examples: 0 positive, 0 negative
% 0.78/0.94  # Parsed axioms                        : 16
% 0.78/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.94  # Initial clauses                      : 51
% 0.78/0.94  # Removed in clause preprocessing      : 0
% 0.78/0.94  # Initial clauses in saturation        : 51
% 0.78/0.94  # Processed clauses                    : 1016
% 0.78/0.94  # ...of these trivial                  : 5
% 0.78/0.94  # ...subsumed                          : 93
% 0.78/0.94  # ...remaining for further processing  : 918
% 0.78/0.94  # Other redundant clauses eliminated   : 0
% 0.78/0.94  # Clauses deleted for lack of memory   : 0
% 0.78/0.94  # Backward-subsumed                    : 534
% 0.78/0.94  # Backward-rewritten                   : 0
% 0.78/0.94  # Generated clauses                    : 1407
% 0.78/0.94  # ...of the previous two non-trivial   : 1249
% 0.78/0.94  # Contextual simplify-reflections      : 176
% 0.78/0.94  # Paramodulations                      : 1398
% 0.78/0.94  # Factorizations                       : 0
% 0.78/0.94  # Equation resolutions                 : 9
% 0.78/0.94  # Propositional unsat checks           : 0
% 0.78/0.94  #    Propositional check models        : 0
% 0.78/0.94  #    Propositional check unsatisfiable : 0
% 0.78/0.94  #    Propositional clauses             : 0
% 0.78/0.94  #    Propositional clauses after purity: 0
% 0.78/0.94  #    Propositional unsat core size     : 0
% 0.78/0.94  #    Propositional preprocessing time  : 0.000
% 0.78/0.94  #    Propositional encoding time       : 0.000
% 0.78/0.94  #    Propositional solver time         : 0.000
% 0.78/0.94  #    Success case prop preproc time    : 0.000
% 0.78/0.94  #    Success case prop encoding time   : 0.000
% 0.78/0.94  #    Success case prop solver time     : 0.000
% 0.78/0.94  # Current number of processed clauses  : 333
% 0.78/0.94  #    Positive orientable unit clauses  : 4
% 0.78/0.94  #    Positive unorientable unit clauses: 0
% 0.78/0.94  #    Negative unit clauses             : 3
% 0.78/0.94  #    Non-unit-clauses                  : 326
% 0.78/0.94  # Current number of unprocessed clauses: 255
% 0.78/0.94  # ...number of literals in the above   : 5605
% 0.78/0.94  # Current number of archived formulas  : 0
% 0.78/0.94  # Current number of archived clauses   : 585
% 0.78/0.94  # Clause-clause subsumption calls (NU) : 270943
% 0.78/0.94  # Rec. Clause-clause subsumption calls : 10361
% 0.78/0.94  # Non-unit clause-clause subsumptions  : 750
% 0.78/0.94  # Unit Clause-clause subsumption calls : 233
% 0.78/0.94  # Rewrite failures with RHS unbound    : 0
% 0.78/0.94  # BW rewrite match attempts            : 0
% 0.78/0.94  # BW rewrite match successes           : 0
% 0.78/0.94  # Condensation attempts                : 0
% 0.78/0.94  # Condensation successes               : 0
% 0.78/0.94  # Termbank termtop insertions          : 171923
% 0.78/0.94  
% 0.78/0.94  # -------------------------------------------------
% 0.78/0.94  # User time                : 0.588 s
% 0.78/0.94  # System time              : 0.010 s
% 0.78/0.94  # Total time               : 0.598 s
% 0.78/0.94  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
