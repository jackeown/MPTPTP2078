%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:08 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 (514595 expanded)
%              Number of clauses        :   85 (167658 expanded)
%              Number of leaves         :   13 (127539 expanded)
%              Depth                    :   27
%              Number of atoms          :  760 (6275058 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).

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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

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
    ! [X42,X43,X46] :
      ( ( m1_subset_1(esk5_2(X42,X43),u1_struct_0(X42))
        | v2_struct_0(X43)
        | ~ v4_orders_2(X43)
        | ~ v7_waybel_0(X43)
        | ~ l1_waybel_0(X43,X42)
        | ~ v1_compts_1(X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( r3_waybel_9(X42,X43,esk5_2(X42,X43))
        | v2_struct_0(X43)
        | ~ v4_orders_2(X43)
        | ~ v7_waybel_0(X43)
        | ~ l1_waybel_0(X43,X42)
        | ~ v1_compts_1(X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( ~ v2_struct_0(esk6_1(X42))
        | v1_compts_1(X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( v4_orders_2(esk6_1(X42))
        | v1_compts_1(X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( v7_waybel_0(esk6_1(X42))
        | v1_compts_1(X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( l1_waybel_0(esk6_1(X42),X42)
        | v1_compts_1(X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( ~ m1_subset_1(X46,u1_struct_0(X42))
        | ~ r3_waybel_9(X42,esk6_1(X42),X46)
        | v1_compts_1(X42)
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).

fof(c_0_15,negated_conjecture,(
    ! [X49,X50] :
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
      & ( ~ m2_yellow_6(X49,esk7_0,esk8_0)
        | ~ v3_yellow_6(X49,esk7_0)
        | ~ v1_compts_1(esk7_0) )
      & ( m2_yellow_6(esk9_1(X50),esk7_0,X50)
        | v2_struct_0(X50)
        | ~ v4_orders_2(X50)
        | ~ v7_waybel_0(X50)
        | ~ l1_waybel_0(X50,esk7_0)
        | v1_compts_1(esk7_0) )
      & ( v3_yellow_6(esk9_1(X50),esk7_0)
        | v2_struct_0(X50)
        | ~ v4_orders_2(X50)
        | ~ v7_waybel_0(X50)
        | ~ l1_waybel_0(X50,esk7_0)
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
    ! [X26,X27,X28] :
      ( ( ~ v2_struct_0(X28)
        | ~ m2_yellow_6(X28,X26,X27)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26) )
      & ( v4_orders_2(X28)
        | ~ m2_yellow_6(X28,X26,X27)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26) )
      & ( v7_waybel_0(X28)
        | ~ m2_yellow_6(X28,X26,X27)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26) )
      & ( l1_waybel_0(X28,X26)
        | ~ m2_yellow_6(X28,X26,X27)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_23,negated_conjecture,
    ( m2_yellow_6(esk9_1(X1),esk7_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk7_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | l1_waybel_0(esk6_1(esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v4_orders_2(esk6_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v7_waybel_0(esk6_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18])]),c_0_19])).

fof(c_0_27,plain,(
    ! [X15,X16,X17,X18,X19,X23] :
      ( ( ~ r2_hidden(X18,X17)
        | ~ m1_connsp_2(X19,X15,X18)
        | r1_waybel_0(X15,X16,X19)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | X17 != k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_connsp_2(esk1_4(X15,X16,X17,X18),X15,X18)
        | r2_hidden(X18,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | X17 != k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r1_waybel_0(X15,X16,esk1_4(X15,X16,X17,X18))
        | r2_hidden(X18,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | X17 != k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))
        | X17 = k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_connsp_2(esk3_3(X15,X16,X17),X15,esk2_3(X15,X16,X17))
        | ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r1_waybel_0(X15,X16,esk3_3(X15,X16,X17))
        | ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X17)
        | ~ m1_connsp_2(X23,X15,esk2_3(X15,X16,X17))
        | r1_waybel_0(X15,X16,X23)
        | X17 = k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_28,plain,(
    ! [X6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_29,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | m2_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0,esk6_1(esk7_0))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

fof(c_0_31,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_32,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ v4_orders_2(X25)
      | ~ v7_waybel_0(X25)
      | ~ l1_waybel_0(X25,X24)
      | m1_subset_1(k10_yellow_6(X24,X25),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

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
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | l1_waybel_0(esk9_1(esk6_1(esk7_0)),esk7_0)
    | v2_struct_0(esk6_1(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19]),c_0_25]),c_0_26]),c_0_24])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v4_orders_2(esk9_1(esk6_1(esk7_0)))
    | v2_struct_0(esk6_1(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_19]),c_0_25]),c_0_26]),c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v7_waybel_0(esk9_1(esk6_1(esk7_0)))
    | v2_struct_0(esk6_1(esk7_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_19]),c_0_25]),c_0_26]),c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v2_struct_0(esk6_1(esk7_0))
    | ~ v2_struct_0(esk9_1(esk6_1(esk7_0)))
    | ~ l1_struct_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_19]),c_0_25]),c_0_26]),c_0_24])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk2_3(X1,X2,k1_xboole_0),u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | l1_waybel_0(esk9_1(esk6_1(esk7_0)),esk7_0)
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_18])])).

cnf(c_0_47,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v4_orders_2(esk9_1(esk6_1(esk7_0)))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_18])])).

cnf(c_0_48,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v7_waybel_0(esk9_1(esk6_1(esk7_0)))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_18])])).

cnf(c_0_49,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v2_struct_0(esk6_1(esk7_0))
    | ~ v2_struct_0(esk9_1(esk6_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_18])])).

fof(c_0_50,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | ~ r1_tarski(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_51,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_52,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | v2_struct_0(esk6_1(esk7_0))
    | m1_subset_1(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_17]),c_0_18])]),c_0_19]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

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
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

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
    inference(split_conjunct,[status(thm)],[c_0_27])).

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
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | m1_connsp_2(esk1_4(esk7_0,esk9_1(esk6_1(esk7_0)),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)),esk7_0,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))
    | v2_struct_0(esk6_1(esk7_0))
    | r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_37])).

fof(c_0_62,plain,(
    ! [X34,X35,X36,X37] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ v4_orders_2(X35)
      | ~ v7_waybel_0(X35)
      | ~ l1_waybel_0(X35,X34)
      | ~ m2_yellow_6(X36,X34,X35)
      | ~ m1_subset_1(X37,u1_struct_0(X34))
      | ~ r3_waybel_9(X34,X36,X37)
      | r3_waybel_9(X34,X35,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

fof(c_0_63,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ v4_orders_2(X32)
      | ~ v7_waybel_0(X32)
      | ~ l1_waybel_0(X32,X31)
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | ~ r2_hidden(X33,k10_yellow_6(X31,X32))
      | r3_waybel_9(X31,X32,X33) ) ),
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_58]),c_0_44])).

cnf(c_0_65,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | r1_waybel_0(esk7_0,esk9_1(esk6_1(esk7_0)),esk1_4(esk7_0,esk9_1(esk6_1(esk7_0)),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)))
    | v2_struct_0(esk6_1(esk7_0))
    | r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_17]),c_0_18]),c_0_37])]),c_0_19]),c_0_61]),c_0_47]),c_0_48]),c_0_46]),c_0_49])).

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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_17]),c_0_18])]),c_0_19]),c_0_53]),c_0_47]),c_0_48]),c_0_46]),c_0_49])).

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
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_53]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))) = k1_xboole_0
    | v1_compts_1(esk7_0)
    | r3_waybel_9(esk7_0,esk9_1(esk6_1(esk7_0)),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_17]),c_0_18])]),c_0_19]),c_0_53]),c_0_47]),c_0_48]),c_0_46]),c_0_49])).

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
    ! [X29,X30] :
      ( ( ~ v3_yellow_6(X30,X29)
        | k10_yellow_6(X29,X30) != k1_xboole_0
        | v2_struct_0(X30)
        | ~ v4_orders_2(X30)
        | ~ v7_waybel_0(X30)
        | ~ l1_waybel_0(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( k10_yellow_6(X29,X30) = k1_xboole_0
        | v3_yellow_6(X30,X29)
        | v2_struct_0(X30)
        | ~ v4_orders_2(X30)
        | ~ v7_waybel_0(X30)
        | ~ l1_waybel_0(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_30]),c_0_25]),c_0_26]),c_0_24])).

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
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_17]),c_0_18])]),c_0_19]),c_0_53])).

cnf(c_0_78,negated_conjecture,
    ( v1_compts_1(esk7_0)
    | v3_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0)
    | v2_struct_0(esk6_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_24]),c_0_25]),c_0_26])).

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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_17]),c_0_18])]),c_0_19]),c_0_47]),c_0_48]),c_0_46]),c_0_78]),c_0_49])).

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
    ! [X38,X39,X40] :
      ( ( m2_yellow_6(esk4_3(X38,X39,X40),X38,X39)
        | ~ r3_waybel_9(X38,X39,X40)
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | v2_struct_0(X39)
        | ~ v4_orders_2(X39)
        | ~ v7_waybel_0(X39)
        | ~ l1_waybel_0(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r2_hidden(X40,k10_yellow_6(X38,esk4_3(X38,X39,X40)))
        | ~ r3_waybel_9(X38,X39,X40)
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | v2_struct_0(X39)
        | ~ v4_orders_2(X39)
        | ~ v7_waybel_0(X39)
        | ~ l1_waybel_0(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
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
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_97]),c_0_88]),c_0_89]),c_0_90])]),c_0_91]),c_0_19])).

cnf(c_0_100,negated_conjecture,
    ( v4_orders_2(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_97]),c_0_88]),c_0_89]),c_0_90])]),c_0_91]),c_0_19])).

cnf(c_0_101,negated_conjecture,
    ( v7_waybel_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_97]),c_0_88]),c_0_89]),c_0_90])]),c_0_91]),c_0_19])).

cnf(c_0_102,negated_conjecture,
    ( ~ v2_struct_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_97]),c_0_88]),c_0_89]),c_0_90])]),c_0_91]),c_0_19])).

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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_39]),c_0_18])])).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.52  #
% 0.20/0.52  # Preprocessing time       : 0.030 s
% 0.20/0.52  # Presaturation interreduction done
% 0.20/0.52  
% 0.20/0.52  # Proof found!
% 0.20/0.52  # SZS status Theorem
% 0.20/0.52  # SZS output start CNFRefutation
% 0.20/0.52  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow19)).
% 0.20/0.52  fof(t35_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_yellow19)).
% 0.20/0.52  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.20/0.52  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.20/0.52  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.52  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.52  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.20/0.52  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.52  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.52  fof(t31_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_waybel_9)).
% 0.20/0.52  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.20/0.52  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.20/0.52  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.20/0.52  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.20/0.52  fof(c_0_14, plain, ![X42, X43, X46]:(((m1_subset_1(esk5_2(X42,X43),u1_struct_0(X42))|(v2_struct_0(X43)|~v4_orders_2(X43)|~v7_waybel_0(X43)|~l1_waybel_0(X43,X42))|~v1_compts_1(X42)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))&(r3_waybel_9(X42,X43,esk5_2(X42,X43))|(v2_struct_0(X43)|~v4_orders_2(X43)|~v7_waybel_0(X43)|~l1_waybel_0(X43,X42))|~v1_compts_1(X42)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))))&(((((~v2_struct_0(esk6_1(X42))|v1_compts_1(X42)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))&(v4_orders_2(esk6_1(X42))|v1_compts_1(X42)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))))&(v7_waybel_0(esk6_1(X42))|v1_compts_1(X42)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))))&(l1_waybel_0(esk6_1(X42),X42)|v1_compts_1(X42)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))))&(~m1_subset_1(X46,u1_struct_0(X42))|~r3_waybel_9(X42,esk6_1(X42),X46)|v1_compts_1(X42)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).
% 0.20/0.52  fof(c_0_15, negated_conjecture, ![X49, X50]:(((~v2_struct_0(esk7_0)&v2_pre_topc(esk7_0))&l1_pre_topc(esk7_0))&((((((~v2_struct_0(esk8_0)|~v1_compts_1(esk7_0))&(v4_orders_2(esk8_0)|~v1_compts_1(esk7_0)))&(v7_waybel_0(esk8_0)|~v1_compts_1(esk7_0)))&(l1_waybel_0(esk8_0,esk7_0)|~v1_compts_1(esk7_0)))&(~m2_yellow_6(X49,esk7_0,esk8_0)|~v3_yellow_6(X49,esk7_0)|~v1_compts_1(esk7_0)))&((m2_yellow_6(esk9_1(X50),esk7_0,X50)|(v2_struct_0(X50)|~v4_orders_2(X50)|~v7_waybel_0(X50)|~l1_waybel_0(X50,esk7_0))|v1_compts_1(esk7_0))&(v3_yellow_6(esk9_1(X50),esk7_0)|(v2_struct_0(X50)|~v4_orders_2(X50)|~v7_waybel_0(X50)|~l1_waybel_0(X50,esk7_0))|v1_compts_1(esk7_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).
% 0.20/0.52  cnf(c_0_16, plain, (l1_waybel_0(esk6_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.52  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_20, plain, (v4_orders_2(esk6_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.52  cnf(c_0_21, plain, (v7_waybel_0(esk6_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.52  fof(c_0_22, plain, ![X26, X27, X28]:((((~v2_struct_0(X28)|~m2_yellow_6(X28,X26,X27)|(v2_struct_0(X26)|~l1_struct_0(X26)|v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26)))&(v4_orders_2(X28)|~m2_yellow_6(X28,X26,X27)|(v2_struct_0(X26)|~l1_struct_0(X26)|v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))))&(v7_waybel_0(X28)|~m2_yellow_6(X28,X26,X27)|(v2_struct_0(X26)|~l1_struct_0(X26)|v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))))&(l1_waybel_0(X28,X26)|~m2_yellow_6(X28,X26,X27)|(v2_struct_0(X26)|~l1_struct_0(X26)|v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.20/0.52  cnf(c_0_23, negated_conjecture, (m2_yellow_6(esk9_1(X1),esk7_0,X1)|v2_struct_0(X1)|v1_compts_1(esk7_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_24, negated_conjecture, (v1_compts_1(esk7_0)|l1_waybel_0(esk6_1(esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.52  cnf(c_0_25, negated_conjecture, (v1_compts_1(esk7_0)|v4_orders_2(esk6_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.52  cnf(c_0_26, negated_conjecture, (v1_compts_1(esk7_0)|v7_waybel_0(esk6_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.52  fof(c_0_27, plain, ![X15, X16, X17, X18, X19, X23]:(((~r2_hidden(X18,X17)|(~m1_connsp_2(X19,X15,X18)|r1_waybel_0(X15,X16,X19))|~m1_subset_1(X18,u1_struct_0(X15))|X17!=k10_yellow_6(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((m1_connsp_2(esk1_4(X15,X16,X17,X18),X15,X18)|r2_hidden(X18,X17)|~m1_subset_1(X18,u1_struct_0(X15))|X17!=k10_yellow_6(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~r1_waybel_0(X15,X16,esk1_4(X15,X16,X17,X18))|r2_hidden(X18,X17)|~m1_subset_1(X18,u1_struct_0(X15))|X17!=k10_yellow_6(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))))&((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))|X17=k10_yellow_6(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(((m1_connsp_2(esk3_3(X15,X16,X17),X15,esk2_3(X15,X16,X17))|~r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k10_yellow_6(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~r1_waybel_0(X15,X16,esk3_3(X15,X16,X17))|~r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k10_yellow_6(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(r2_hidden(esk2_3(X15,X16,X17),X17)|(~m1_connsp_2(X23,X15,esk2_3(X15,X16,X17))|r1_waybel_0(X15,X16,X23))|X17=k10_yellow_6(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~l1_waybel_0(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.20/0.52  fof(c_0_28, plain, ![X6]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.52  cnf(c_0_29, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.52  cnf(c_0_30, negated_conjecture, (v1_compts_1(esk7_0)|m2_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0,esk6_1(esk7_0))|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.52  fof(c_0_31, plain, ![X14]:(~l1_pre_topc(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.52  cnf(c_0_32, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.52  cnf(c_0_33, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.52  cnf(c_0_34, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.52  fof(c_0_35, plain, ![X24, X25]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24)|m1_subset_1(k10_yellow_6(X24,X25),k1_zfmisc_1(u1_struct_0(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.20/0.52  cnf(c_0_36, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.52  cnf(c_0_37, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.52  cnf(c_0_38, negated_conjecture, (v1_compts_1(esk7_0)|l1_waybel_0(esk9_1(esk6_1(esk7_0)),esk7_0)|v2_struct_0(esk6_1(esk7_0))|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_19]), c_0_25]), c_0_26]), c_0_24])).
% 0.20/0.52  cnf(c_0_39, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.52  cnf(c_0_40, negated_conjecture, (v1_compts_1(esk7_0)|v4_orders_2(esk9_1(esk6_1(esk7_0)))|v2_struct_0(esk6_1(esk7_0))|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_19]), c_0_25]), c_0_26]), c_0_24])).
% 0.20/0.52  cnf(c_0_41, negated_conjecture, (v1_compts_1(esk7_0)|v7_waybel_0(esk9_1(esk6_1(esk7_0)))|v2_struct_0(esk6_1(esk7_0))|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_30]), c_0_19]), c_0_25]), c_0_26]), c_0_24])).
% 0.20/0.52  cnf(c_0_42, negated_conjecture, (v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))|~v2_struct_0(esk9_1(esk6_1(esk7_0)))|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_30]), c_0_19]), c_0_25]), c_0_26]), c_0_24])).
% 0.20/0.52  cnf(c_0_43, plain, (m1_connsp_2(esk1_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.52  cnf(c_0_44, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.52  cnf(c_0_45, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk2_3(X1,X2,k1_xboole_0),u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.52  cnf(c_0_46, negated_conjecture, (v1_compts_1(esk7_0)|l1_waybel_0(esk9_1(esk6_1(esk7_0)),esk7_0)|v2_struct_0(esk6_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_18])])).
% 0.20/0.52  cnf(c_0_47, negated_conjecture, (v1_compts_1(esk7_0)|v4_orders_2(esk9_1(esk6_1(esk7_0)))|v2_struct_0(esk6_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_18])])).
% 0.20/0.52  cnf(c_0_48, negated_conjecture, (v1_compts_1(esk7_0)|v7_waybel_0(esk9_1(esk6_1(esk7_0)))|v2_struct_0(esk6_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_18])])).
% 0.20/0.52  cnf(c_0_49, negated_conjecture, (v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))|~v2_struct_0(esk9_1(esk6_1(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_39]), c_0_18])])).
% 0.20/0.52  fof(c_0_50, plain, ![X12, X13]:(~r2_hidden(X12,X13)|~r1_tarski(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.52  fof(c_0_51, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.52  cnf(c_0_52, plain, (m1_connsp_2(esk1_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)|v2_struct_0(X2)|v2_struct_0(X1)|r2_hidden(X3,k10_yellow_6(X1,X2))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]), c_0_44])).
% 0.20/0.52  cnf(c_0_53, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))|m1_subset_1(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_17]), c_0_18])]), c_0_19]), c_0_47]), c_0_48]), c_0_49])).
% 0.20/0.52  cnf(c_0_54, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.52  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.52  cnf(c_0_56, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|m1_connsp_2(esk1_4(esk7_0,X1,k10_yellow_6(esk7_0,X1),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)),esk7_0,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))|v2_struct_0(X1)|r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,X1))|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.52  cnf(c_0_57, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.52  cnf(c_0_58, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk1_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.52  cnf(c_0_59, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r1_waybel_0(X1,X2,X4)|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X4,X1,esk2_3(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.52  cnf(c_0_60, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|m1_connsp_2(esk1_4(esk7_0,esk9_1(esk6_1(esk7_0)),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)),esk7_0,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))|r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.20/0.52  cnf(c_0_61, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_37])).
% 0.20/0.52  fof(c_0_62, plain, ![X34, X35, X36, X37]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34)|(~m2_yellow_6(X36,X34,X35)|(~m1_subset_1(X37,u1_struct_0(X34))|(~r3_waybel_9(X34,X36,X37)|r3_waybel_9(X34,X35,X37)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).
% 0.20/0.52  fof(c_0_63, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31)|(~m1_subset_1(X33,u1_struct_0(X31))|(~r2_hidden(X33,k10_yellow_6(X31,X32))|r3_waybel_9(X31,X32,X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.20/0.52  cnf(c_0_64, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(X3,k10_yellow_6(X2,X1))|~r1_waybel_0(X2,X1,esk1_4(X2,X1,k10_yellow_6(X2,X1),X3))|~l1_waybel_0(X1,X2)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_58]), c_0_44])).
% 0.20/0.52  cnf(c_0_65, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r1_waybel_0(esk7_0,esk9_1(esk6_1(esk7_0)),esk1_4(esk7_0,esk9_1(esk6_1(esk7_0)),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0)))|v2_struct_0(esk6_1(esk7_0))|r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_17]), c_0_18]), c_0_37])]), c_0_19]), c_0_61]), c_0_47]), c_0_48]), c_0_46]), c_0_49])).
% 0.20/0.52  cnf(c_0_66, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~r3_waybel_9(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.52  cnf(c_0_67, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.52  cnf(c_0_68, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))|r2_hidden(esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0),k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_17]), c_0_18])]), c_0_19]), c_0_53]), c_0_47]), c_0_48]), c_0_46]), c_0_49])).
% 0.20/0.52  cnf(c_0_69, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r3_waybel_9(esk7_0,X1,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))|v2_struct_0(X1)|~r3_waybel_9(esk7_0,X2,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|~m2_yellow_6(X2,esk7_0,X1)|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_53]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.52  cnf(c_0_70, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r3_waybel_9(esk7_0,esk9_1(esk6_1(esk7_0)),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_17]), c_0_18])]), c_0_19]), c_0_53]), c_0_47]), c_0_48]), c_0_46]), c_0_49])).
% 0.20/0.52  cnf(c_0_71, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r3_waybel_9(esk7_0,X1,esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))|v2_struct_0(X1)|~m2_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0,X1)|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.52  fof(c_0_72, plain, ![X29, X30]:((~v3_yellow_6(X30,X29)|k10_yellow_6(X29,X30)!=k1_xboole_0|(v2_struct_0(X30)|~v4_orders_2(X30)|~v7_waybel_0(X30)|~l1_waybel_0(X30,X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(k10_yellow_6(X29,X30)=k1_xboole_0|v3_yellow_6(X30,X29)|(v2_struct_0(X30)|~v4_orders_2(X30)|~v7_waybel_0(X30)|~l1_waybel_0(X30,X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.20/0.52  cnf(c_0_73, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk6_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.52  cnf(c_0_74, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|r3_waybel_9(esk7_0,esk6_1(esk7_0),esk2_3(esk7_0,esk9_1(esk6_1(esk7_0)),k1_xboole_0))|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_30]), c_0_25]), c_0_26]), c_0_24])).
% 0.20/0.52  cnf(c_0_75, negated_conjecture, (v3_yellow_6(esk9_1(X1),esk7_0)|v2_struct_0(X1)|v1_compts_1(esk7_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_76, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.52  cnf(c_0_77, negated_conjecture, (k10_yellow_6(esk7_0,esk9_1(esk6_1(esk7_0)))=k1_xboole_0|v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_17]), c_0_18])]), c_0_19]), c_0_53])).
% 0.20/0.52  cnf(c_0_78, negated_conjecture, (v1_compts_1(esk7_0)|v3_yellow_6(esk9_1(esk6_1(esk7_0)),esk7_0)|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.52  cnf(c_0_79, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk6_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.52  cnf(c_0_80, negated_conjecture, (v1_compts_1(esk7_0)|v2_struct_0(esk6_1(esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_17]), c_0_18])]), c_0_19]), c_0_47]), c_0_48]), c_0_46]), c_0_78]), c_0_49])).
% 0.20/0.52  cnf(c_0_81, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_82, negated_conjecture, (v1_compts_1(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.52  cnf(c_0_83, negated_conjecture, (v7_waybel_0(esk8_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_84, negated_conjecture, (v4_orders_2(esk8_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_85, negated_conjecture, (~v2_struct_0(esk8_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  fof(c_0_86, plain, ![X38, X39, X40]:((m2_yellow_6(esk4_3(X38,X39,X40),X38,X39)|~r3_waybel_9(X38,X39,X40)|~m1_subset_1(X40,u1_struct_0(X38))|(v2_struct_0(X39)|~v4_orders_2(X39)|~v7_waybel_0(X39)|~l1_waybel_0(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(r2_hidden(X40,k10_yellow_6(X38,esk4_3(X38,X39,X40)))|~r3_waybel_9(X38,X39,X40)|~m1_subset_1(X40,u1_struct_0(X38))|(v2_struct_0(X39)|~v4_orders_2(X39)|~v7_waybel_0(X39)|~l1_waybel_0(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.20/0.52  cnf(c_0_87, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.52  cnf(c_0_88, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.20/0.52  cnf(c_0_89, negated_conjecture, (v7_waybel_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_82])])).
% 0.20/0.52  cnf(c_0_90, negated_conjecture, (v4_orders_2(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_82])])).
% 0.20/0.52  cnf(c_0_91, negated_conjecture, (~v2_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_82])])).
% 0.20/0.52  cnf(c_0_92, plain, (m2_yellow_6(esk4_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.52  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk5_2(esk7_0,esk8_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_82]), c_0_89]), c_0_90]), c_0_17]), c_0_18])]), c_0_91]), c_0_19])).
% 0.20/0.52  cnf(c_0_94, plain, (r3_waybel_9(X1,X2,esk5_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.52  cnf(c_0_95, negated_conjecture, (m2_yellow_6(esk4_3(esk7_0,X1,esk5_2(esk7_0,esk8_0)),esk7_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk7_0,X1,esk5_2(esk7_0,esk8_0))|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.52  cnf(c_0_96, negated_conjecture, (r3_waybel_9(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_88]), c_0_82]), c_0_89]), c_0_90]), c_0_17]), c_0_18])]), c_0_91]), c_0_19])).
% 0.20/0.52  cnf(c_0_97, negated_conjecture, (m2_yellow_6(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_88]), c_0_89]), c_0_90])]), c_0_91])).
% 0.20/0.52  cnf(c_0_98, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.52  cnf(c_0_99, negated_conjecture, (l1_waybel_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0)|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_97]), c_0_88]), c_0_89]), c_0_90])]), c_0_91]), c_0_19])).
% 0.20/0.52  cnf(c_0_100, negated_conjecture, (v4_orders_2(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_97]), c_0_88]), c_0_89]), c_0_90])]), c_0_91]), c_0_19])).
% 0.20/0.52  cnf(c_0_101, negated_conjecture, (v7_waybel_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_97]), c_0_88]), c_0_89]), c_0_90])]), c_0_91]), c_0_19])).
% 0.20/0.52  cnf(c_0_102, negated_conjecture, (~v2_struct_0(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_97]), c_0_88]), c_0_89]), c_0_90])]), c_0_91]), c_0_19])).
% 0.20/0.52  cnf(c_0_103, plain, (r2_hidden(X1,k10_yellow_6(X2,esk4_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.52  cnf(c_0_104, negated_conjecture, (~m2_yellow_6(X1,esk7_0,esk8_0)|~v3_yellow_6(X1,esk7_0)|~v1_compts_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_105, negated_conjecture, (k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))=k1_xboole_0|v3_yellow_6(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0)|~l1_struct_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_17]), c_0_18])]), c_0_19]), c_0_100]), c_0_101]), c_0_102])).
% 0.20/0.52  cnf(c_0_106, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk5_2(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk4_3(esk7_0,X1,esk5_2(esk7_0,esk8_0))))|~r3_waybel_9(esk7_0,X1,esk5_2(esk7_0,esk8_0))|~l1_waybel_0(X1,esk7_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_93]), c_0_17]), c_0_18])]), c_0_19])).
% 0.20/0.52  cnf(c_0_107, negated_conjecture, (~v3_yellow_6(X1,esk7_0)|~m2_yellow_6(X1,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_82])])).
% 0.20/0.52  cnf(c_0_108, negated_conjecture, (k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))=k1_xboole_0|v3_yellow_6(esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_39]), c_0_18])])).
% 0.20/0.52  cnf(c_0_109, negated_conjecture, (r2_hidden(esk5_2(esk7_0,esk8_0),k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_96]), c_0_88]), c_0_89]), c_0_90])]), c_0_91])).
% 0.20/0.52  cnf(c_0_110, negated_conjecture, (k10_yellow_6(esk7_0,esk4_3(esk7_0,esk8_0,esk5_2(esk7_0,esk8_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_97])])).
% 0.20/0.52  cnf(c_0_111, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_61]), ['proof']).
% 0.20/0.52  # SZS output end CNFRefutation
% 0.20/0.52  # Proof object total steps             : 112
% 0.20/0.52  # Proof object clause steps            : 85
% 0.20/0.52  # Proof object formula steps           : 27
% 0.20/0.52  # Proof object conjectures             : 57
% 0.20/0.52  # Proof object clause conjectures      : 54
% 0.20/0.52  # Proof object formula conjectures     : 3
% 0.20/0.52  # Proof object initial clauses used    : 36
% 0.20/0.52  # Proof object initial formulas used   : 13
% 0.20/0.52  # Proof object generating inferences   : 41
% 0.20/0.52  # Proof object simplifying inferences  : 189
% 0.20/0.52  # Training examples: 0 positive, 0 negative
% 0.20/0.52  # Parsed axioms                        : 14
% 0.20/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.52  # Initial clauses                      : 41
% 0.20/0.52  # Removed in clause preprocessing      : 0
% 0.20/0.52  # Initial clauses in saturation        : 41
% 0.20/0.52  # Processed clauses                    : 631
% 0.20/0.52  # ...of these trivial                  : 0
% 0.20/0.52  # ...subsumed                          : 44
% 0.20/0.52  # ...remaining for further processing  : 587
% 0.20/0.52  # Other redundant clauses eliminated   : 3
% 0.20/0.52  # Clauses deleted for lack of memory   : 0
% 0.20/0.52  # Backward-subsumed                    : 453
% 0.20/0.52  # Backward-rewritten                   : 16
% 0.20/0.52  # Generated clauses                    : 1300
% 0.20/0.52  # ...of the previous two non-trivial   : 1240
% 0.20/0.52  # Contextual simplify-reflections      : 753
% 0.20/0.52  # Paramodulations                      : 1297
% 0.20/0.52  # Factorizations                       : 0
% 0.20/0.52  # Equation resolutions                 : 3
% 0.20/0.52  # Propositional unsat checks           : 0
% 0.20/0.52  #    Propositional check models        : 0
% 0.20/0.52  #    Propositional check unsatisfiable : 0
% 0.20/0.52  #    Propositional clauses             : 0
% 0.20/0.52  #    Propositional clauses after purity: 0
% 0.20/0.52  #    Propositional unsat core size     : 0
% 0.20/0.52  #    Propositional preprocessing time  : 0.000
% 0.20/0.52  #    Propositional encoding time       : 0.000
% 0.20/0.52  #    Propositional solver time         : 0.000
% 0.20/0.52  #    Success case prop preproc time    : 0.000
% 0.20/0.52  #    Success case prop encoding time   : 0.000
% 0.20/0.52  #    Success case prop solver time     : 0.000
% 0.20/0.52  # Current number of processed clauses  : 74
% 0.20/0.52  #    Positive orientable unit clauses  : 12
% 0.20/0.52  #    Positive unorientable unit clauses: 0
% 0.20/0.52  #    Negative unit clauses             : 4
% 0.20/0.52  #    Non-unit-clauses                  : 58
% 0.20/0.52  # Current number of unprocessed clauses: 14
% 0.20/0.52  # ...number of literals in the above   : 85
% 0.20/0.52  # Current number of archived formulas  : 0
% 0.20/0.52  # Current number of archived clauses   : 510
% 0.20/0.52  # Clause-clause subsumption calls (NU) : 213742
% 0.20/0.52  # Rec. Clause-clause subsumption calls : 4791
% 0.20/0.52  # Non-unit clause-clause subsumptions  : 1244
% 0.20/0.52  # Unit Clause-clause subsumption calls : 28
% 0.20/0.52  # Rewrite failures with RHS unbound    : 0
% 0.20/0.52  # BW rewrite match attempts            : 3
% 0.20/0.52  # BW rewrite match successes           : 2
% 0.20/0.52  # Condensation attempts                : 0
% 0.20/0.52  # Condensation successes               : 0
% 0.20/0.52  # Termbank termtop insertions          : 116975
% 0.20/0.52  
% 0.20/0.52  # -------------------------------------------------
% 0.20/0.52  # User time                : 0.175 s
% 0.20/0.52  # System time              : 0.007 s
% 0.20/0.52  # Total time               : 0.182 s
% 0.20/0.52  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
