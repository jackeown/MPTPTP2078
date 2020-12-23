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

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  112 (516611 expanded)
%              Number of clauses        :   85 (168666 expanded)
%              Number of leaves         :   13 (128043 expanded)
%              Depth                    :   27
%              Number of atoms          :  759 (6279492 expanded)
%              Number of equality atoms :   31 (9602 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   81 (   5 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X39,X40,X43] :
      ( ( m1_subset_1(esk5_2(X39,X40),u1_struct_0(X39))
        | v2_struct_0(X40)
        | ~ v4_orders_2(X40)
        | ~ v7_waybel_0(X40)
        | ~ l1_waybel_0(X40,X39)
        | ~ v1_compts_1(X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( r3_waybel_9(X39,X40,esk5_2(X39,X40))
        | v2_struct_0(X40)
        | ~ v4_orders_2(X40)
        | ~ v7_waybel_0(X40)
        | ~ l1_waybel_0(X40,X39)
        | ~ v1_compts_1(X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ v2_struct_0(esk6_1(X39))
        | v1_compts_1(X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v4_orders_2(esk6_1(X39))
        | v1_compts_1(X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v7_waybel_0(esk6_1(X39))
        | v1_compts_1(X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( l1_waybel_0(esk6_1(X39),X39)
        | v1_compts_1(X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ m1_subset_1(X43,u1_struct_0(X39))
        | ~ r3_waybel_9(X39,esk6_1(X39),X43)
        | v1_compts_1(X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).

fof(c_0_15,negated_conjecture,(
    ! [X46,X47] :
      ( ~ v2_struct_0(esk7_0)
      & v2_pre_topc(esk7_0)
      & l1_pre_topc(esk7_0)
      & ( ~ v2_struct_0(esk8_0)
        | ~ v1_compts_1(esk7_0) )
      & ( v4_orders_2(esk8_0)
        | ~ v1_compts_1(esk7_0) )
      & ( v7_waybel_0(esk8_0)
        | ~ v1_compts_1(esk7_0) )
      & ( l1_waybel_0(esk8_0,esk7_0)
        | ~ v1_compts_1(esk7_0) )
      & ( ~ m2_yellow_6(X46,esk7_0,esk8_0)
        | ~ v3_yellow_6(X46,esk7_0)
        | ~ v1_compts_1(esk7_0) )
      & ( m2_yellow_6(esk9_1(X47),esk7_0,X47)
        | v2_struct_0(X47)
        | ~ v4_orders_2(X47)
        | ~ v7_waybel_0(X47)
        | ~ l1_waybel_0(X47,esk7_0)
        | v1_compts_1(esk7_0) )
      & ( v3_yellow_6(esk9_1(X47),esk7_0)
        | v2_struct_0(X47)
        | ~ v4_orders_2(X47)
        | ~ v7_waybel_0(X47)
        | ~ l1_waybel_0(X47,esk7_0)
        | v1_compts_1(esk7_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).

cnf(c_0_16,plain,
    ( l1_waybel_0(esk6_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v4_orders_2(esk6_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v7_waybel_0(esk6_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_23,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_24,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v2_struct_0(X25)
        | ~ m2_yellow_6(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23) )
      & ( v4_orders_2(X25)
        | ~ m2_yellow_6(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23) )
      & ( v7_waybel_0(X25)
        | ~ m2_yellow_6(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23) )
      & ( l1_waybel_0(X25,X23)
        | ~ m2_yellow_6(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_25,negated_conjecture,
    ( m2_yellow_6(esk9_1(X1),esk7_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk7_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | l1_waybel_0(esk6_1(esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v4_orders_2(esk6_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v7_waybel_0(esk6_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18])]),c_0_19])).

fof(c_0_29,plain,(
    ! [X12,X13,X14,X15,X16,X20] :
      ( ( ~ r2_hidden(X15,X14)
        | ~ m1_connsp_2(X16,X12,X15)
        | r1_waybel_0(X12,X13,X16)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | X14 != k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_connsp_2(esk1_4(X12,X13,X14,X15),X12,X15)
        | r2_hidden(X15,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | X14 != k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r1_waybel_0(X12,X13,esk1_4(X12,X13,X14,X15))
        | r2_hidden(X15,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | X14 != k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))
        | X14 = k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_connsp_2(esk3_3(X12,X13,X14),X12,esk2_3(X12,X13,X14))
        | ~ r2_hidden(esk2_3(X12,X13,X14),X14)
        | X14 = k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r1_waybel_0(X12,X13,esk3_3(X12,X13,X14))
        | ~ r2_hidden(esk2_3(X12,X13,X14),X14)
        | X14 = k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X14)
        | ~ m1_connsp_2(X20,X12,esk2_3(X12,X13,X14))
        | r1_waybel_0(X12,X13,X20)
        | X14 = k10_yellow_6(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | m2_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0,esk6_1(esk7_0))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

fof(c_0_34,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_38,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | v2_struct_0(X22)
      | ~ v4_orders_2(X22)
      | ~ v7_waybel_0(X22)
      | ~ l1_waybel_0(X22,X21)
      | m1_subset_1(k10_yellow_6(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | l1_waybel_0(esk9_1(esk6_1(esk7_0)),esk7_0)
    | v2_struct_0(esk6_1(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_19]),c_0_27]),c_0_28]),c_0_26])).

cnf(c_0_42,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v4_orders_2(esk9_1(esk6_1(esk7_0)))
    | v2_struct_0(esk6_1(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_19]),c_0_27]),c_0_28]),c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v7_waybel_0(esk9_1(esk6_1(esk7_0)))
    | v2_struct_0(esk6_1(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_19]),c_0_27]),c_0_28]),c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v2_struct_0(esk6_1(esk7_0))
    | ~ v2_struct_0(esk9_1(esk6_1(esk7_0)))
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_19]),c_0_27]),c_0_28]),c_0_26])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk2_3(X1,X2,k1_xboole_0),u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | l1_waybel_0(esk9_1(esk6_1(esk7_0)),esk7_0)
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_18])])).

cnf(c_0_50,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v4_orders_2(esk9_1(esk6_1(esk7_0)))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_18])])).

cnf(c_0_51,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v7_waybel_0(esk9_1(esk6_1(esk7_0)))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_42]),c_0_18])])).

cnf(c_0_52,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v2_struct_0(esk6_1(esk7_0))
    | ~ v2_struct_0(esk9_1(esk6_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_18])])).

cnf(c_0_53,plain,
    ( m1_connsp_2(esk1_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | v2_struct_0(esk6_1(esk7_0))
    | m1_subset_1(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_17]),c_0_18])]),c_0_19]),c_0_50]),c_0_51]),c_0_52])).

fof(c_0_55,plain,(
    ! [X9,X10] :
      ( ~ r2_hidden(X9,X10)
      | ~ r1_tarski(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_56,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | m1_connsp_2(esk1_4(esk7_0,X1,k10_yellow_6(esk7_0,X1),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)),esk7_0,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))
    | v2_struct_0(esk6_1(esk7_0))
    | v2_struct_0(X1)
    | r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,X1))
    | ~ l1_waybel_0(X1,esk7_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_58,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_59,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_60,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | m1_connsp_2(esk1_4(esk7_0,esk9_1(esk6_1(esk7_0)),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)),esk7_0,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))
    | v2_struct_0(esk6_1(esk7_0))
    | r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_31])).

fof(c_0_62,plain,(
    ! [X31,X32,X33,X34] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ v4_orders_2(X32)
      | ~ v7_waybel_0(X32)
      | ~ l1_waybel_0(X32,X31)
      | ~ m2_yellow_6(X33,X31,X32)
      | ~ m1_subset_1(X34,u1_struct_0(X31))
      | ~ r3_waybel_9(X31,X33,X34)
      | r3_waybel_9(X31,X32,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

fof(c_0_63,plain,(
    ! [X28,X29,X30] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ v4_orders_2(X29)
      | ~ v7_waybel_0(X29)
      | ~ l1_waybel_0(X29,X28)
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ r2_hidden(X30,k10_yellow_6(X28,X29))
      | r3_waybel_9(X28,X29,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(X3,k10_yellow_6(X2,X1))
    | ~ r1_waybel_0(X2,X1,esk1_4(X2,X1,k10_yellow_6(X2,X1),X3))
    | ~ l1_waybel_0(X1,X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_58]),c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | r1_waybel_0(esk7_0,esk9_1(esk6_1(esk7_0)),esk1_4(esk7_0,esk9_1(esk6_1(esk7_0)),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)))
    | v2_struct_0(esk6_1(esk7_0))
    | r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_17]),c_0_18]),c_0_40])]),c_0_19]),c_0_61]),c_0_50]),c_0_51]),c_0_49]),c_0_52])).

cnf(c_0_66,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | v2_struct_0(esk6_1(esk7_0))
    | r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_17]),c_0_18])]),c_0_19]),c_0_54]),c_0_50]),c_0_51]),c_0_49]),c_0_52])).

cnf(c_0_69,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | r3_waybel_9(esk7_0,X1,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))
    | v2_struct_0(esk6_1(esk7_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk7_0,X2,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))
    | ~ m2_yellow_6(X2,esk7_0,X1)
    | ~ l1_waybel_0(X1,esk7_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_54]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | r3_waybel_9(esk7_0,esk9_1(esk6_1(esk7_0)),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_17]),c_0_18])]),c_0_19]),c_0_54]),c_0_50]),c_0_51]),c_0_49]),c_0_52])).

cnf(c_0_71,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | r3_waybel_9(esk7_0,X1,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))
    | v2_struct_0(esk6_1(esk7_0))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0,X1)
    | ~ l1_waybel_0(X1,esk7_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_72,plain,(
    ! [X26,X27] :
      ( ( ~ v3_yellow_6(X27,X26)
        | k10_yellow_6(X26,X27) != k1_xboole_0
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( k10_yellow_6(X26,X27) = k1_xboole_0
        | v3_yellow_6(X27,X26)
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

cnf(c_0_73,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk6_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_74,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | r3_waybel_9(esk7_0,esk6_1(esk7_0),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_33]),c_0_27]),c_0_28]),c_0_26])).

cnf(c_0_75,negated_conjecture,
    ( v3_yellow_6(esk9_1(X1),esk7_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk7_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_17]),c_0_18])]),c_0_19]),c_0_54])).

cnf(c_0_78,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v3_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0)
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_79,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk6_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_80,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_17]),c_0_18])]),c_0_19]),c_0_50]),c_0_51]),c_0_49]),c_0_78]),c_0_52])).

cnf(c_0_81,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0)
    | ~ v1_compts_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_82,negated_conjecture,
    ( v1_compts_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_83,negated_conjecture,
    ( v7_waybel_0(esk8_0)
    | ~ v1_compts_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_84,negated_conjecture,
    ( v4_orders_2(esk8_0)
    | ~ v1_compts_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_85,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    | ~ v1_compts_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_86,plain,(
    ! [X35,X36,X37] :
      ( ( m2_yellow_6(esk4_3(X35,X36,X37),X35,X36)
        | ~ r3_waybel_9(X35,X36,X37)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | v2_struct_0(X36)
        | ~ v4_orders_2(X36)
        | ~ v7_waybel_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(X37,k10_yellow_6(X35,esk4_3(X35,X36,X37)))
        | ~ r3_waybel_9(X35,X36,X37)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | v2_struct_0(X36)
        | ~ v4_orders_2(X36)
        | ~ v7_waybel_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_87,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_88,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_89,negated_conjecture,
    ( v7_waybel_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_82])])).

cnf(c_0_90,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_82])])).

cnf(c_0_91,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_82])])).

cnf(c_0_92,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk5_2(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_82]),c_0_89]),c_0_90]),c_0_17]),c_0_18])]),c_0_91]),c_0_19])).

cnf(c_0_94,plain,
    ( r3_waybel_9(X1,X2,esk5_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_95,negated_conjecture,
    ( m2_yellow_6(esk4_3(esk7_0,X1,esk5_2(esk7_0,esk8_0)),esk7_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk7_0,X1,esk5_2(esk7_0,esk8_0))
    | ~ l1_waybel_0(X1,esk7_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_96,negated_conjecture,
    ( r3_waybel_9(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_88]),c_0_82]),c_0_89]),c_0_90]),c_0_17]),c_0_18])]),c_0_91]),c_0_19])).

cnf(c_0_97,negated_conjecture,
    ( m2_yellow_6(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_88]),c_0_89]),c_0_90])]),c_0_91])).

cnf(c_0_98,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_99,negated_conjecture,
    ( l1_waybel_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_97]),c_0_88]),c_0_89]),c_0_90])]),c_0_91]),c_0_19])).

cnf(c_0_100,negated_conjecture,
    ( v4_orders_2(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_97]),c_0_88]),c_0_89]),c_0_90])]),c_0_91]),c_0_19])).

cnf(c_0_101,negated_conjecture,
    ( v7_waybel_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_97]),c_0_88]),c_0_89]),c_0_90])]),c_0_91]),c_0_19])).

cnf(c_0_102,negated_conjecture,
    ( ~ v2_struct_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_97]),c_0_88]),c_0_89]),c_0_90])]),c_0_91]),c_0_19])).

cnf(c_0_103,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_104,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk7_0,esk8_0)
    | ~ v3_yellow_6(X1,esk7_0)
    | ~ v1_compts_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_105,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0))) = k1_xboole_0
    | v3_yellow_6(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_17]),c_0_18])]),c_0_19]),c_0_100]),c_0_101]),c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk5_2(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk4_3(esk7_0,X1,esk5_2(esk7_0,esk8_0))))
    | ~ r3_waybel_9(esk7_0,X1,esk5_2(esk7_0,esk8_0))
    | ~ l1_waybel_0(X1,esk7_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_93]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_107,negated_conjecture,
    ( ~ v3_yellow_6(X1,esk7_0)
    | ~ m2_yellow_6(X1,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_82])])).

cnf(c_0_108,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0))) = k1_xboole_0
    | v3_yellow_6(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_42]),c_0_18])])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk5_2(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_96]),c_0_88]),c_0_89]),c_0_90])]),c_0_91])).

cnf(c_0_110,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_97])])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:46:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.56  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.56  #
% 0.19/0.56  # Preprocessing time       : 0.042 s
% 0.19/0.56  # Presaturation interreduction done
% 0.19/0.56  
% 0.19/0.56  # Proof found!
% 0.19/0.56  # SZS status Theorem
% 0.19/0.56  # SZS output start CNFRefutation
% 0.19/0.56  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 0.19/0.56  fof(t35_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_yellow19)).
% 0.19/0.56  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.56  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.56  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.19/0.56  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.19/0.56  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.56  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.19/0.56  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.56  fof(t31_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 0.19/0.56  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.19/0.56  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.19/0.56  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.19/0.56  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.19/0.56  fof(c_0_14, plain, ![X39, X40, X43]:(((m1_subset_1(esk5_2(X39,X40),u1_struct_0(X39))|(v2_struct_0(X40)|~v4_orders_2(X40)|~v7_waybel_0(X40)|~l1_waybel_0(X40,X39))|~v1_compts_1(X39)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(r3_waybel_9(X39,X40,esk5_2(X39,X40))|(v2_struct_0(X40)|~v4_orders_2(X40)|~v7_waybel_0(X40)|~l1_waybel_0(X40,X39))|~v1_compts_1(X39)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(((((~v2_struct_0(esk6_1(X39))|v1_compts_1(X39)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(v4_orders_2(esk6_1(X39))|v1_compts_1(X39)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(v7_waybel_0(esk6_1(X39))|v1_compts_1(X39)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(l1_waybel_0(esk6_1(X39),X39)|v1_compts_1(X39)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(~m1_subset_1(X43,u1_struct_0(X39))|~r3_waybel_9(X39,esk6_1(X39),X43)|v1_compts_1(X39)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).
% 0.19/0.56  fof(c_0_15, negated_conjecture, ![X46, X47]:(((~v2_struct_0(esk7_0)&v2_pre_topc(esk7_0))&l1_pre_topc(esk7_0))&((((((~v2_struct_0(esk8_0)|~v1_compts_1(esk7_0))&(v4_orders_2(esk8_0)|~v1_compts_1(esk7_0)))&(v7_waybel_0(esk8_0)|~v1_compts_1(esk7_0)))&(l1_waybel_0(esk8_0,esk7_0)|~v1_compts_1(esk7_0)))&(~m2_yellow_6(X46,esk7_0,esk8_0)|~v3_yellow_6(X46,esk7_0)|~v1_compts_1(esk7_0)))&((m2_yellow_6(esk9_1(X47),esk7_0,X47)|(v2_struct_0(X47)|~v4_orders_2(X47)|~v7_waybel_0(X47)|~l1_waybel_0(X47,esk7_0))|v1_compts_1(esk7_0))&(v3_yellow_6(esk9_1(X47),esk7_0)|(v2_struct_0(X47)|~v4_orders_2(X47)|~v7_waybel_0(X47)|~l1_waybel_0(X47,esk7_0))|v1_compts_1(esk7_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).
% 0.19/0.56  cnf(c_0_16, plain, (l1_waybel_0(esk6_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.56  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  cnf(c_0_20, plain, (v4_orders_2(esk6_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.56  cnf(c_0_21, plain, (v7_waybel_0(esk6_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.56  fof(c_0_22, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.56  fof(c_0_23, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.56  fof(c_0_24, plain, ![X23, X24, X25]:((((~v2_struct_0(X25)|~m2_yellow_6(X25,X23,X24)|(v2_struct_0(X23)|~l1_struct_0(X23)|v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23)))&(v4_orders_2(X25)|~m2_yellow_6(X25,X23,X24)|(v2_struct_0(X23)|~l1_struct_0(X23)|v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23))))&(v7_waybel_0(X25)|~m2_yellow_6(X25,X23,X24)|(v2_struct_0(X23)|~l1_struct_0(X23)|v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23))))&(l1_waybel_0(X25,X23)|~m2_yellow_6(X25,X23,X24)|(v2_struct_0(X23)|~l1_struct_0(X23)|v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.19/0.56  cnf(c_0_25, negated_conjecture, (m2_yellow_6(esk9_1(X1),esk7_0,X1)|v2_struct_0(X1)|v1_compts_1(esk7_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  cnf(c_0_26, negated_conjecture, (v1_compts_1(esk7_0)|l1_waybel_0(esk6_1(esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.56  cnf(c_0_27, negated_conjecture, (v1_compts_1(esk7_0)|v4_orders_2(esk6_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.56  cnf(c_0_28, negated_conjecture, (v1_compts_1(esk7_0)|v7_waybel_0(esk6_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.56  fof(c_0_29, plain, ![X12, X13, X14, X15, X16, X20]:(((~r2_hidden(X15,X14)|(~m1_connsp_2(X16,X12,X15)|r1_waybel_0(X12,X13,X16))|~m1_subset_1(X15,u1_struct_0(X12))|X14!=k10_yellow_6(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&((m1_connsp_2(esk1_4(X12,X13,X14,X15),X12,X15)|r2_hidden(X15,X14)|~m1_subset_1(X15,u1_struct_0(X12))|X14!=k10_yellow_6(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r1_waybel_0(X12,X13,esk1_4(X12,X13,X14,X15))|r2_hidden(X15,X14)|~m1_subset_1(X15,u1_struct_0(X12))|X14!=k10_yellow_6(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))))&((m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))|X14=k10_yellow_6(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(((m1_connsp_2(esk3_3(X12,X13,X14),X12,esk2_3(X12,X13,X14))|~r2_hidden(esk2_3(X12,X13,X14),X14)|X14=k10_yellow_6(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r1_waybel_0(X12,X13,esk3_3(X12,X13,X14))|~r2_hidden(esk2_3(X12,X13,X14),X14)|X14=k10_yellow_6(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(r2_hidden(esk2_3(X12,X13,X14),X14)|(~m1_connsp_2(X20,X12,esk2_3(X12,X13,X14))|r1_waybel_0(X12,X13,X20))|X14=k10_yellow_6(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X13)|~v4_orders_2(X13)|~v7_waybel_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.19/0.56  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.56  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.56  cnf(c_0_32, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.56  cnf(c_0_33, negated_conjecture, (v1_compts_1(esk7_0)|m2_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0,esk6_1(esk7_0))|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.56  fof(c_0_34, plain, ![X11]:(~l1_pre_topc(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.56  cnf(c_0_35, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.56  cnf(c_0_36, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.56  cnf(c_0_37, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.56  fof(c_0_38, plain, ![X21, X22]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21)|m1_subset_1(k10_yellow_6(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.19/0.56  cnf(c_0_39, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.56  cnf(c_0_40, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.56  cnf(c_0_41, negated_conjecture, (v1_compts_1(esk7_0)|l1_waybel_0(esk9_1(esk6_1(esk7_0)),esk7_0)|v2_struct_0(esk6_1(esk7_0))|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_19]), c_0_27]), c_0_28]), c_0_26])).
% 0.19/0.56  cnf(c_0_42, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.56  cnf(c_0_43, negated_conjecture, (v1_compts_1(esk7_0)|v4_orders_2(esk9_1(esk6_1(esk7_0)))|v2_struct_0(esk6_1(esk7_0))|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_33]), c_0_19]), c_0_27]), c_0_28]), c_0_26])).
% 0.19/0.56  cnf(c_0_44, negated_conjecture, (v1_compts_1(esk7_0)|v7_waybel_0(esk9_1(esk6_1(esk7_0)))|v2_struct_0(esk6_1(esk7_0))|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_19]), c_0_27]), c_0_28]), c_0_26])).
% 0.19/0.56  cnf(c_0_45, negated_conjecture, (v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))|~v2_struct_0(esk9_1(esk6_1(esk7_0)))|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_19]), c_0_27]), c_0_28]), c_0_26])).
% 0.19/0.56  cnf(c_0_46, plain, (m1_connsp_2(esk1_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.56  cnf(c_0_47, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.56  cnf(c_0_48, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk2_3(X1,X2,k1_xboole_0),u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.56  cnf(c_0_49, negated_conjecture, (v1_compts_1(esk7_0)|l1_waybel_0(esk9_1(esk6_1(esk7_0)),esk7_0)|v2_struct_0(esk6_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_18])])).
% 0.19/0.56  cnf(c_0_50, negated_conjecture, (v1_compts_1(esk7_0)|v4_orders_2(esk9_1(esk6_1(esk7_0)))|v2_struct_0(esk6_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_42]), c_0_18])])).
% 0.19/0.56  cnf(c_0_51, negated_conjecture, (v1_compts_1(esk7_0)|v7_waybel_0(esk9_1(esk6_1(esk7_0)))|v2_struct_0(esk6_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_42]), c_0_18])])).
% 0.19/0.56  cnf(c_0_52, negated_conjecture, (v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))|~v2_struct_0(esk9_1(esk6_1(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_42]), c_0_18])])).
% 0.19/0.56  cnf(c_0_53, plain, (m1_connsp_2(esk1_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)|v2_struct_0(X2)|v2_struct_0(X1)|r2_hidden(X3,k10_yellow_6(X1,X2))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]), c_0_47])).
% 0.19/0.56  cnf(c_0_54, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))|m1_subset_1(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_17]), c_0_18])]), c_0_19]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.56  fof(c_0_55, plain, ![X9, X10]:(~r2_hidden(X9,X10)|~r1_tarski(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.56  cnf(c_0_56, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|m1_connsp_2(esk1_4(esk7_0,X1,k10_yellow_6(esk7_0,X1),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)),esk7_0,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))|v2_struct_0(X1)|r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,X1))|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.56  cnf(c_0_57, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.56  cnf(c_0_58, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk1_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.56  cnf(c_0_59, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r1_waybel_0(X1,X2,X4)|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X4,X1,esk2_3(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.56  cnf(c_0_60, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|m1_connsp_2(esk1_4(esk7_0,esk9_1(esk6_1(esk7_0)),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)),esk7_0,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))|r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.56  cnf(c_0_61, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_31])).
% 0.19/0.56  fof(c_0_62, plain, ![X31, X32, X33, X34]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31)|(~m2_yellow_6(X33,X31,X32)|(~m1_subset_1(X34,u1_struct_0(X31))|(~r3_waybel_9(X31,X33,X34)|r3_waybel_9(X31,X32,X34)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).
% 0.19/0.56  fof(c_0_63, plain, ![X28, X29, X30]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28)|(~m1_subset_1(X30,u1_struct_0(X28))|(~r2_hidden(X30,k10_yellow_6(X28,X29))|r3_waybel_9(X28,X29,X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.19/0.56  cnf(c_0_64, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(X3,k10_yellow_6(X2,X1))|~r1_waybel_0(X2,X1,esk1_4(X2,X1,k10_yellow_6(X2,X1),X3))|~l1_waybel_0(X1,X2)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_58]), c_0_47])).
% 0.19/0.56  cnf(c_0_65, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r1_waybel_0(esk7_0,esk9_1(esk6_1(esk7_0)),esk1_4(esk7_0,esk9_1(esk6_1(esk7_0)),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)))|v2_struct_0(esk6_1(esk7_0))|r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_17]), c_0_18]), c_0_40])]), c_0_19]), c_0_61]), c_0_50]), c_0_51]), c_0_49]), c_0_52])).
% 0.19/0.56  cnf(c_0_66, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~r3_waybel_9(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.56  cnf(c_0_67, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.56  cnf(c_0_68, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))|r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_17]), c_0_18])]), c_0_19]), c_0_54]), c_0_50]), c_0_51]), c_0_49]), c_0_52])).
% 0.19/0.56  cnf(c_0_69, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r3_waybel_9(esk7_0,X1,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))|v2_struct_0(X1)|~r3_waybel_9(esk7_0,X2,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|~m2_yellow_6(X2,esk7_0,X1)|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_54]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.56  cnf(c_0_70, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r3_waybel_9(esk7_0,esk9_1(esk6_1(esk7_0)),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_17]), c_0_18])]), c_0_19]), c_0_54]), c_0_50]), c_0_51]), c_0_49]), c_0_52])).
% 0.19/0.56  cnf(c_0_71, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r3_waybel_9(esk7_0,X1,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))|v2_struct_0(X1)|~m2_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0,X1)|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.56  fof(c_0_72, plain, ![X26, X27]:((~v3_yellow_6(X27,X26)|k10_yellow_6(X26,X27)!=k1_xboole_0|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(k10_yellow_6(X26,X27)=k1_xboole_0|v3_yellow_6(X27,X26)|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.19/0.56  cnf(c_0_73, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk6_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.56  cnf(c_0_74, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r3_waybel_9(esk7_0,esk6_1(esk7_0),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_33]), c_0_27]), c_0_28]), c_0_26])).
% 0.19/0.56  cnf(c_0_75, negated_conjecture, (v3_yellow_6(esk9_1(X1),esk7_0)|v2_struct_0(X1)|v1_compts_1(esk7_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  cnf(c_0_76, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.56  cnf(c_0_77, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_17]), c_0_18])]), c_0_19]), c_0_54])).
% 0.19/0.56  cnf(c_0_78, negated_conjecture, (v1_compts_1(esk7_0)|v3_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0)|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.56  cnf(c_0_79, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk6_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.56  cnf(c_0_80, negated_conjecture, (v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_17]), c_0_18])]), c_0_19]), c_0_50]), c_0_51]), c_0_49]), c_0_78]), c_0_52])).
% 0.19/0.56  cnf(c_0_81, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  cnf(c_0_82, negated_conjecture, (v1_compts_1(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.56  cnf(c_0_83, negated_conjecture, (v7_waybel_0(esk8_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  cnf(c_0_84, negated_conjecture, (v4_orders_2(esk8_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  cnf(c_0_85, negated_conjecture, (~v2_struct_0(esk8_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  fof(c_0_86, plain, ![X35, X36, X37]:((m2_yellow_6(esk4_3(X35,X36,X37),X35,X36)|~r3_waybel_9(X35,X36,X37)|~m1_subset_1(X37,u1_struct_0(X35))|(v2_struct_0(X36)|~v4_orders_2(X36)|~v7_waybel_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(r2_hidden(X37,k10_yellow_6(X35,esk4_3(X35,X36,X37)))|~r3_waybel_9(X35,X36,X37)|~m1_subset_1(X37,u1_struct_0(X35))|(v2_struct_0(X36)|~v4_orders_2(X36)|~v7_waybel_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.19/0.56  cnf(c_0_87, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.56  cnf(c_0_88, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.19/0.56  cnf(c_0_89, negated_conjecture, (v7_waybel_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_82])])).
% 0.19/0.56  cnf(c_0_90, negated_conjecture, (v4_orders_2(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_82])])).
% 0.19/0.56  cnf(c_0_91, negated_conjecture, (~v2_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_82])])).
% 0.19/0.56  cnf(c_0_92, plain, (m2_yellow_6(esk4_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.56  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk5_2(esk7_0,esk8_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_82]), c_0_89]), c_0_90]), c_0_17]), c_0_18])]), c_0_91]), c_0_19])).
% 0.19/0.56  cnf(c_0_94, plain, (r3_waybel_9(X1,X2,esk5_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.56  cnf(c_0_95, negated_conjecture, (m2_yellow_6(esk4_3(esk7_0,X1,esk5_2(esk7_0,esk8_0)),esk7_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk7_0,X1,esk5_2(esk7_0,esk8_0))|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.56  cnf(c_0_96, negated_conjecture, (r3_waybel_9(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_88]), c_0_82]), c_0_89]), c_0_90]), c_0_17]), c_0_18])]), c_0_91]), c_0_19])).
% 0.19/0.56  cnf(c_0_97, negated_conjecture, (m2_yellow_6(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_88]), c_0_89]), c_0_90])]), c_0_91])).
% 0.19/0.56  cnf(c_0_98, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.56  cnf(c_0_99, negated_conjecture, (l1_waybel_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0)|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_97]), c_0_88]), c_0_89]), c_0_90])]), c_0_91]), c_0_19])).
% 0.19/0.56  cnf(c_0_100, negated_conjecture, (v4_orders_2(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_97]), c_0_88]), c_0_89]), c_0_90])]), c_0_91]), c_0_19])).
% 0.19/0.56  cnf(c_0_101, negated_conjecture, (v7_waybel_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_97]), c_0_88]), c_0_89]), c_0_90])]), c_0_91]), c_0_19])).
% 0.19/0.56  cnf(c_0_102, negated_conjecture, (~v2_struct_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_97]), c_0_88]), c_0_89]), c_0_90])]), c_0_91]), c_0_19])).
% 0.19/0.56  cnf(c_0_103, plain, (r2_hidden(X1,k10_yellow_6(X2,esk4_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.56  cnf(c_0_104, negated_conjecture, (~m2_yellow_6(X1,esk7_0,esk8_0)|~v3_yellow_6(X1,esk7_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.56  cnf(c_0_105, negated_conjecture, (k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))=k1_xboole_0|v3_yellow_6(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0)|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_17]), c_0_18])]), c_0_19]), c_0_100]), c_0_101]), c_0_102])).
% 0.19/0.56  cnf(c_0_106, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk5_2(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk4_3(esk7_0,X1,esk5_2(esk7_0,esk8_0))))|~r3_waybel_9(esk7_0,X1,esk5_2(esk7_0,esk8_0))|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_93]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.56  cnf(c_0_107, negated_conjecture, (~v3_yellow_6(X1,esk7_0)|~m2_yellow_6(X1,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_82])])).
% 0.19/0.56  cnf(c_0_108, negated_conjecture, (k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))=k1_xboole_0|v3_yellow_6(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_42]), c_0_18])])).
% 0.19/0.56  cnf(c_0_109, negated_conjecture, (r2_hidden(esk5_2(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_96]), c_0_88]), c_0_89]), c_0_90])]), c_0_91])).
% 0.19/0.56  cnf(c_0_110, negated_conjecture, (k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_97])])).
% 0.19/0.56  cnf(c_0_111, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_61]), ['proof']).
% 0.19/0.56  # SZS output end CNFRefutation
% 0.19/0.56  # Proof object total steps             : 112
% 0.19/0.56  # Proof object clause steps            : 85
% 0.19/0.56  # Proof object formula steps           : 27
% 0.19/0.56  # Proof object conjectures             : 57
% 0.19/0.56  # Proof object clause conjectures      : 54
% 0.19/0.56  # Proof object formula conjectures     : 3
% 0.19/0.56  # Proof object initial clauses used    : 36
% 0.19/0.56  # Proof object initial formulas used   : 13
% 0.19/0.56  # Proof object generating inferences   : 41
% 0.19/0.56  # Proof object simplifying inferences  : 189
% 0.19/0.56  # Training examples: 0 positive, 0 negative
% 0.19/0.56  # Parsed axioms                        : 13
% 0.19/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.56  # Initial clauses                      : 40
% 0.19/0.56  # Removed in clause preprocessing      : 0
% 0.19/0.56  # Initial clauses in saturation        : 40
% 0.19/0.56  # Processed clauses                    : 609
% 0.19/0.56  # ...of these trivial                  : 0
% 0.19/0.56  # ...subsumed                          : 41
% 0.19/0.56  # ...remaining for further processing  : 568
% 0.19/0.56  # Other redundant clauses eliminated   : 3
% 0.19/0.56  # Clauses deleted for lack of memory   : 0
% 0.19/0.56  # Backward-subsumed                    : 435
% 0.19/0.56  # Backward-rewritten                   : 16
% 0.19/0.56  # Generated clauses                    : 1269
% 0.19/0.56  # ...of the previous two non-trivial   : 1207
% 0.19/0.56  # Contextual simplify-reflections      : 739
% 0.19/0.56  # Paramodulations                      : 1266
% 0.19/0.56  # Factorizations                       : 0
% 0.19/0.56  # Equation resolutions                 : 3
% 0.19/0.56  # Propositional unsat checks           : 0
% 0.19/0.56  #    Propositional check models        : 0
% 0.19/0.56  #    Propositional check unsatisfiable : 0
% 0.19/0.56  #    Propositional clauses             : 0
% 0.19/0.56  #    Propositional clauses after purity: 0
% 0.19/0.56  #    Propositional unsat core size     : 0
% 0.19/0.56  #    Propositional preprocessing time  : 0.000
% 0.19/0.56  #    Propositional encoding time       : 0.000
% 0.19/0.56  #    Propositional solver time         : 0.000
% 0.19/0.56  #    Success case prop preproc time    : 0.000
% 0.19/0.56  #    Success case prop encoding time   : 0.000
% 0.19/0.56  #    Success case prop solver time     : 0.000
% 0.19/0.56  # Current number of processed clauses  : 74
% 0.19/0.56  #    Positive orientable unit clauses  : 13
% 0.19/0.56  #    Positive unorientable unit clauses: 0
% 0.19/0.56  #    Negative unit clauses             : 4
% 0.19/0.56  #    Non-unit-clauses                  : 57
% 0.19/0.56  # Current number of unprocessed clauses: 11
% 0.19/0.56  # ...number of literals in the above   : 65
% 0.19/0.56  # Current number of archived formulas  : 0
% 0.19/0.56  # Current number of archived clauses   : 491
% 0.19/0.56  # Clause-clause subsumption calls (NU) : 206052
% 0.19/0.56  # Rec. Clause-clause subsumption calls : 3858
% 0.19/0.56  # Non-unit clause-clause subsumptions  : 1210
% 0.19/0.56  # Unit Clause-clause subsumption calls : 29
% 0.19/0.56  # Rewrite failures with RHS unbound    : 0
% 0.19/0.56  # BW rewrite match attempts            : 3
% 0.19/0.56  # BW rewrite match successes           : 2
% 0.19/0.56  # Condensation attempts                : 0
% 0.19/0.56  # Condensation successes               : 0
% 0.19/0.56  # Termbank termtop insertions          : 115446
% 0.19/0.56  
% 0.19/0.56  # -------------------------------------------------
% 0.19/0.56  # User time                : 0.209 s
% 0.19/0.56  # System time              : 0.009 s
% 0.19/0.56  # Total time               : 0.218 s
% 0.19/0.56  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
