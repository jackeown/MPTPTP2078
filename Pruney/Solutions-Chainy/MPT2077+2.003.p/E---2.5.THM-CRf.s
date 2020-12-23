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
% DateTime   : Thu Dec  3 11:22:05 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  117 (143260 expanded)
%              Number of clauses        :   84 (47073 expanded)
%              Number of leaves         :   16 (35482 expanded)
%              Depth                    :   21
%              Number of atoms          :  660 (1761602 expanded)
%              Number of equality atoms :   13 ( 588 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   51 (   4 average)
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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X43,X44,X47] :
      ( ( m1_subset_1(esk4_2(X43,X44),u1_struct_0(X43))
        | ~ r2_hidden(X44,k6_yellow_6(X43))
        | v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X43)
        | ~ v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( r3_waybel_9(X43,X44,esk4_2(X43,X44))
        | ~ r2_hidden(X44,k6_yellow_6(X43))
        | v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X43)
        | ~ v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( ~ v2_struct_0(esk5_1(X43))
        | v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( v4_orders_2(esk5_1(X43))
        | v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( v7_waybel_0(esk5_1(X43))
        | v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( l1_waybel_0(esk5_1(X43),X43)
        | v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( r2_hidden(esk5_1(X43),k6_yellow_6(X43))
        | v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( ~ m1_subset_1(X47,u1_struct_0(X43))
        | ~ r3_waybel_9(X43,esk5_1(X43),X47)
        | v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_yellow19])])])])])])).

fof(c_0_18,negated_conjecture,(
    ! [X50,X51] :
      ( ~ v2_struct_0(esk6_0)
      & v2_pre_topc(esk6_0)
      & l1_pre_topc(esk6_0)
      & ( ~ v2_struct_0(esk7_0)
        | ~ v1_compts_1(esk6_0) )
      & ( v4_orders_2(esk7_0)
        | ~ v1_compts_1(esk6_0) )
      & ( v7_waybel_0(esk7_0)
        | ~ v1_compts_1(esk6_0) )
      & ( l1_waybel_0(esk7_0,esk6_0)
        | ~ v1_compts_1(esk6_0) )
      & ( ~ m2_yellow_6(X50,esk6_0,esk7_0)
        | ~ v3_yellow_6(X50,esk6_0)
        | ~ v1_compts_1(esk6_0) )
      & ( m2_yellow_6(esk8_1(X51),esk6_0,X51)
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ v7_waybel_0(X51)
        | ~ l1_waybel_0(X51,esk6_0)
        | v1_compts_1(esk6_0) )
      & ( v3_yellow_6(esk8_1(X51),esk6_0)
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ v7_waybel_0(X51)
        | ~ l1_waybel_0(X51,esk6_0)
        | v1_compts_1(esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

cnf(c_0_19,plain,
    ( l1_waybel_0(esk5_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v4_orders_2(esk5_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v7_waybel_0(esk5_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_26,plain,(
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

cnf(c_0_27,negated_conjecture,
    ( m2_yellow_6(esk8_1(X1),esk6_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk6_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_31,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_33,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_34,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | v2_struct_0(X23)
      | ~ v4_orders_2(X23)
      | ~ v7_waybel_0(X23)
      | ~ l1_waybel_0(X23,X22)
      | m1_subset_1(k10_yellow_6(X22,X23),k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_35,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21])).

cnf(c_0_38,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),c_0_22]),c_0_29]),c_0_30]),c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_37])]),c_0_22]),c_0_29]),c_0_30]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_36]),c_0_37])]),c_0_22]),c_0_29]),c_0_30]),c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | ~ v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_37])]),c_0_22]),c_0_29]),c_0_30]),c_0_28])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_20]),c_0_21])]),c_0_22]),c_0_46]),c_0_47]),c_0_48])).

fof(c_0_53,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | v2_struct_0(X30)
      | ~ v4_orders_2(X30)
      | ~ v7_waybel_0(X30)
      | ~ l1_waybel_0(X30,X29)
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | ~ r2_hidden(X31,k10_yellow_6(X29,X30))
      | r3_waybel_9(X29,X30,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

fof(c_0_54,plain,(
    ! [X32,X33,X34,X35] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ v4_orders_2(X33)
      | ~ v7_waybel_0(X33)
      | ~ l1_waybel_0(X33,X32)
      | ~ m2_yellow_6(X34,X32,X33)
      | ~ m1_subset_1(X35,u1_struct_0(X32))
      | ~ r3_waybel_9(X32,X34,X35)
      | r3_waybel_9(X32,X33,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
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

cnf(c_0_58,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( r3_waybel_9(X1,X2,esk1_2(k10_yellow_6(X1,X2),X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tarski(k10_yellow_6(X1,X2),X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk1_2(k10_yellow_6(X1,X2),X3),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_50])).

fof(c_0_61,plain,(
    ! [X13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_62,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2)
    | ~ r3_waybel_9(esk6_0,X3,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))
    | ~ m2_yellow_6(X3,esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_20]),c_0_21])]),c_0_22]),c_0_46]),c_0_47]),c_0_45]),c_0_48])).

fof(c_0_64,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_65,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2)
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_65])).

cnf(c_0_69,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk5_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_36]),c_0_29]),c_0_30]),c_0_28])).

fof(c_0_71,plain,(
    ! [X40,X41] :
      ( ( m1_subset_1(esk3_2(X40,X41),u1_struct_0(X40))
        | v2_struct_0(X41)
        | ~ v4_orders_2(X41)
        | ~ v7_waybel_0(X41)
        | ~ l1_waybel_0(X41,X40)
        | ~ v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r3_waybel_9(X40,X41,esk3_2(X40,X41))
        | v2_struct_0(X41)
        | ~ v4_orders_2(X41)
        | ~ v7_waybel_0(X41)
        | ~ l1_waybel_0(X41,X40)
        | ~ v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).

fof(c_0_72,plain,(
    ! [X27,X28] :
      ( ( ~ v3_yellow_6(X28,X27)
        | k10_yellow_6(X27,X28) != k1_xboole_0
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( k10_yellow_6(X27,X28) = k1_xboole_0
        | v3_yellow_6(X28,X27)
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_20]),c_0_21])]),c_0_22]),c_0_59])).

cnf(c_0_75,negated_conjecture,
    ( v3_yellow_6(esk8_1(X1),esk6_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk6_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_76,plain,(
    ! [X36,X37,X38] :
      ( ( m2_yellow_6(esk2_3(X36,X37,X38),X36,X37)
        | ~ r3_waybel_9(X36,X37,X38)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | v2_struct_0(X37)
        | ~ v4_orders_2(X37)
        | ~ v7_waybel_0(X37)
        | ~ l1_waybel_0(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( r2_hidden(X38,k10_yellow_6(X36,esk2_3(X36,X37,X38)))
        | ~ r3_waybel_9(X36,X37,X38)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | v2_struct_0(X37)
        | ~ v4_orders_2(X37)
        | ~ v7_waybel_0(X37)
        | ~ l1_waybel_0(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_81,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_82,plain,
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

cnf(c_0_83,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_85,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v1_compts_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_20]),c_0_21])]),c_0_22]),c_0_79]),c_0_80]),c_0_81])).

cnf(c_0_87,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk5_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_88,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_20]),c_0_21])]),c_0_22]),c_0_46]),c_0_47]),c_0_45]),c_0_84]),c_0_48])).

cnf(c_0_89,plain,
    ( r3_waybel_9(X1,X2,esk3_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_90,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_91,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,X1,esk3_2(esk6_0,esk7_0)),esk6_0,X1)
    | v2_struct_0(X1)
    | ~ v1_compts_1(esk6_0)
    | ~ r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_92,negated_conjecture,
    ( v1_compts_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_93,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | ~ v1_compts_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_78]),c_0_20]),c_0_21])]),c_0_22]),c_0_79]),c_0_80]),c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,X1,esk3_2(esk6_0,esk7_0))))
    | ~ v1_compts_1(esk6_0)
    | ~ r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_86]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_95,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,X1,esk3_2(esk6_0,esk7_0)),esk6_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_96,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_92])])).

cnf(c_0_97,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_92])])).

cnf(c_0_98,negated_conjecture,
    ( v7_waybel_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_92])])).

cnf(c_0_99,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_92])])).

cnf(c_0_100,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_92])])).

cnf(c_0_101,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_102,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | ~ r1_tarski(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_103,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,X1,esk3_2(esk6_0,esk7_0))))
    | ~ r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,esk7_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_92])])).

cnf(c_0_104,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),c_0_98]),c_0_99])]),c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_92])])).

cnf(c_0_106,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_96]),c_0_97]),c_0_98]),c_0_99])]),c_0_100])).

cnf(c_0_108,plain,
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

cnf(c_0_109,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_104]),c_0_97]),c_0_98]),c_0_99]),c_0_37])]),c_0_100]),c_0_22])).

cnf(c_0_110,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_104]),c_0_97]),c_0_98]),c_0_99]),c_0_37])]),c_0_100]),c_0_22])).

cnf(c_0_111,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_104]),c_0_97]),c_0_98]),c_0_99]),c_0_37])]),c_0_100]),c_0_22])).

cnf(c_0_112,negated_conjecture,
    ( ~ v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_104])).

cnf(c_0_113,negated_conjecture,
    ( ~ v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_104]),c_0_97]),c_0_98]),c_0_99]),c_0_37])]),c_0_100]),c_0_22])).

cnf(c_0_114,negated_conjecture,
    ( ~ r1_tarski(k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))),esk3_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_115,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110]),c_0_111]),c_0_20]),c_0_21])]),c_0_112]),c_0_113]),c_0_22])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.37/0.63  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.37/0.63  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.37/0.63  #
% 0.37/0.63  # Preprocessing time       : 0.049 s
% 0.37/0.63  # Presaturation interreduction done
% 0.37/0.63  
% 0.37/0.63  # Proof found!
% 0.37/0.63  # SZS status Theorem
% 0.37/0.63  # SZS output start CNFRefutation
% 0.37/0.63  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 0.37/0.63  fof(t36_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>~((r2_hidden(X2,k6_yellow_6(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r3_waybel_9(X1,X2,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_yellow19)).
% 0.37/0.63  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.37/0.63  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.37/0.63  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.37/0.63  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.37/0.63  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.37/0.63  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.37/0.63  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.37/0.63  fof(t31_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 0.37/0.63  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.37/0.63  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.37/0.63  fof(l37_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l37_yellow19)).
% 0.37/0.63  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.37/0.63  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.37/0.63  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.37/0.63  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.37/0.63  fof(c_0_17, plain, ![X43, X44, X47]:(((m1_subset_1(esk4_2(X43,X44),u1_struct_0(X43))|~r2_hidden(X44,k6_yellow_6(X43))|(v2_struct_0(X44)|~v4_orders_2(X44)|~v7_waybel_0(X44)|~l1_waybel_0(X44,X43))|~v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))&(r3_waybel_9(X43,X44,esk4_2(X43,X44))|~r2_hidden(X44,k6_yellow_6(X43))|(v2_struct_0(X44)|~v4_orders_2(X44)|~v7_waybel_0(X44)|~l1_waybel_0(X44,X43))|~v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(((((~v2_struct_0(esk5_1(X43))|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))&(v4_orders_2(esk5_1(X43))|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(v7_waybel_0(esk5_1(X43))|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(l1_waybel_0(esk5_1(X43),X43)|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&((r2_hidden(esk5_1(X43),k6_yellow_6(X43))|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))&(~m1_subset_1(X47,u1_struct_0(X43))|~r3_waybel_9(X43,esk5_1(X43),X47)|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_yellow19])])])])])])).
% 0.37/0.63  fof(c_0_18, negated_conjecture, ![X50, X51]:(((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&((((((~v2_struct_0(esk7_0)|~v1_compts_1(esk6_0))&(v4_orders_2(esk7_0)|~v1_compts_1(esk6_0)))&(v7_waybel_0(esk7_0)|~v1_compts_1(esk6_0)))&(l1_waybel_0(esk7_0,esk6_0)|~v1_compts_1(esk6_0)))&(~m2_yellow_6(X50,esk6_0,esk7_0)|~v3_yellow_6(X50,esk6_0)|~v1_compts_1(esk6_0)))&((m2_yellow_6(esk8_1(X51),esk6_0,X51)|(v2_struct_0(X51)|~v4_orders_2(X51)|~v7_waybel_0(X51)|~l1_waybel_0(X51,esk6_0))|v1_compts_1(esk6_0))&(v3_yellow_6(esk8_1(X51),esk6_0)|(v2_struct_0(X51)|~v4_orders_2(X51)|~v7_waybel_0(X51)|~l1_waybel_0(X51,esk6_0))|v1_compts_1(esk6_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).
% 0.37/0.63  cnf(c_0_19, plain, (l1_waybel_0(esk5_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.63  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  cnf(c_0_23, plain, (v4_orders_2(esk5_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.63  cnf(c_0_24, plain, (v7_waybel_0(esk5_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.63  fof(c_0_25, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.37/0.63  fof(c_0_26, plain, ![X24, X25, X26]:((((~v2_struct_0(X26)|~m2_yellow_6(X26,X24,X25)|(v2_struct_0(X24)|~l1_struct_0(X24)|v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24)))&(v4_orders_2(X26)|~m2_yellow_6(X26,X24,X25)|(v2_struct_0(X24)|~l1_struct_0(X24)|v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24))))&(v7_waybel_0(X26)|~m2_yellow_6(X26,X24,X25)|(v2_struct_0(X24)|~l1_struct_0(X24)|v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24))))&(l1_waybel_0(X26,X24)|~m2_yellow_6(X26,X24,X25)|(v2_struct_0(X24)|~l1_struct_0(X24)|v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.37/0.63  cnf(c_0_27, negated_conjecture, (m2_yellow_6(esk8_1(X1),esk6_0,X1)|v2_struct_0(X1)|v1_compts_1(esk6_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  cnf(c_0_28, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])]), c_0_22])).
% 0.37/0.63  cnf(c_0_29, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_21])]), c_0_22])).
% 0.37/0.63  cnf(c_0_30, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_20]), c_0_21])]), c_0_22])).
% 0.37/0.63  cnf(c_0_31, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.63  fof(c_0_32, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.37/0.63  fof(c_0_33, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.37/0.63  fof(c_0_34, plain, ![X22, X23]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22)|m1_subset_1(k10_yellow_6(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.37/0.63  cnf(c_0_35, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.63  cnf(c_0_36, negated_conjecture, (v1_compts_1(esk6_0)|m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])).
% 0.37/0.63  cnf(c_0_37, negated_conjecture, (l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_21])).
% 0.37/0.63  cnf(c_0_38, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.63  cnf(c_0_39, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.63  cnf(c_0_40, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.63  cnf(c_0_41, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.37/0.63  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.37/0.63  fof(c_0_43, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.37/0.63  cnf(c_0_44, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.63  cnf(c_0_45, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])]), c_0_22]), c_0_29]), c_0_30]), c_0_28])).
% 0.37/0.63  cnf(c_0_46, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_36]), c_0_37])]), c_0_22]), c_0_29]), c_0_30]), c_0_28])).
% 0.37/0.63  cnf(c_0_47, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_36]), c_0_37])]), c_0_22]), c_0_29]), c_0_30]), c_0_28])).
% 0.37/0.63  cnf(c_0_48, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|~v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_37])]), c_0_22]), c_0_29]), c_0_30]), c_0_28])).
% 0.37/0.63  cnf(c_0_49, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.37/0.63  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.63  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.37/0.63  cnf(c_0_52, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_20]), c_0_21])]), c_0_22]), c_0_46]), c_0_47]), c_0_48])).
% 0.37/0.63  fof(c_0_53, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(v2_struct_0(X30)|~v4_orders_2(X30)|~v7_waybel_0(X30)|~l1_waybel_0(X30,X29)|(~m1_subset_1(X31,u1_struct_0(X29))|(~r2_hidden(X31,k10_yellow_6(X29,X30))|r3_waybel_9(X29,X30,X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.37/0.63  fof(c_0_54, plain, ![X32, X33, X34, X35]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32)|(~m2_yellow_6(X34,X32,X33)|(~m1_subset_1(X35,u1_struct_0(X32))|(~r3_waybel_9(X32,X34,X35)|r3_waybel_9(X32,X33,X35)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).
% 0.37/0.63  cnf(c_0_55, plain, (m1_subset_1(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.37/0.63  cnf(c_0_56, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.37/0.63  cnf(c_0_57, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.37/0.63  cnf(c_0_58, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~r3_waybel_9(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.37/0.63  cnf(c_0_59, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.37/0.63  cnf(c_0_60, plain, (r3_waybel_9(X1,X2,esk1_2(k10_yellow_6(X1,X2),X3))|v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(k10_yellow_6(X1,X2),X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(k10_yellow_6(X1,X2),X3),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_57, c_0_50])).
% 0.37/0.63  fof(c_0_61, plain, ![X13]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.37/0.63  cnf(c_0_62, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2)|~r3_waybel_9(esk6_0,X3,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))|~m2_yellow_6(X3,esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_20]), c_0_21])]), c_0_22])).
% 0.37/0.63  cnf(c_0_63, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_59]), c_0_20]), c_0_21])]), c_0_22]), c_0_46]), c_0_47]), c_0_45]), c_0_48])).
% 0.37/0.63  fof(c_0_64, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.37/0.63  cnf(c_0_65, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.37/0.63  cnf(c_0_66, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2)|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.37/0.63  cnf(c_0_67, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.37/0.63  cnf(c_0_68, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_65])).
% 0.37/0.63  cnf(c_0_69, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk5_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.63  cnf(c_0_70, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_36]), c_0_29]), c_0_30]), c_0_28])).
% 0.37/0.63  fof(c_0_71, plain, ![X40, X41]:((m1_subset_1(esk3_2(X40,X41),u1_struct_0(X40))|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X40))|~v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(r3_waybel_9(X40,X41,esk3_2(X40,X41))|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X40))|~v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).
% 0.37/0.63  fof(c_0_72, plain, ![X27, X28]:((~v3_yellow_6(X28,X27)|k10_yellow_6(X27,X28)!=k1_xboole_0|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(k10_yellow_6(X27,X28)=k1_xboole_0|v3_yellow_6(X28,X27)|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.37/0.63  cnf(c_0_73, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.37/0.63  cnf(c_0_74, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_20]), c_0_21])]), c_0_22]), c_0_59])).
% 0.37/0.63  cnf(c_0_75, negated_conjecture, (v3_yellow_6(esk8_1(X1),esk6_0)|v2_struct_0(X1)|v1_compts_1(esk6_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  fof(c_0_76, plain, ![X36, X37, X38]:((m2_yellow_6(esk2_3(X36,X37,X38),X36,X37)|~r3_waybel_9(X36,X37,X38)|~m1_subset_1(X38,u1_struct_0(X36))|(v2_struct_0(X37)|~v4_orders_2(X37)|~v7_waybel_0(X37)|~l1_waybel_0(X37,X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(r2_hidden(X38,k10_yellow_6(X36,esk2_3(X36,X37,X38)))|~r3_waybel_9(X36,X37,X38)|~m1_subset_1(X38,u1_struct_0(X36))|(v2_struct_0(X37)|~v4_orders_2(X37)|~v7_waybel_0(X37)|~l1_waybel_0(X37,X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.37/0.63  cnf(c_0_77, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.37/0.63  cnf(c_0_78, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  cnf(c_0_79, negated_conjecture, (v4_orders_2(esk7_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  cnf(c_0_80, negated_conjecture, (v7_waybel_0(esk7_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  cnf(c_0_81, negated_conjecture, (~v2_struct_0(esk7_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  cnf(c_0_82, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.37/0.63  cnf(c_0_83, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.37/0.63  cnf(c_0_84, negated_conjecture, (v1_compts_1(esk6_0)|v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_28]), c_0_29]), c_0_30])).
% 0.37/0.63  cnf(c_0_85, plain, (m2_yellow_6(esk2_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.37/0.63  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~v1_compts_1(esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_20]), c_0_21])]), c_0_22]), c_0_79]), c_0_80]), c_0_81])).
% 0.37/0.63  cnf(c_0_87, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk5_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.63  cnf(c_0_88, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_20]), c_0_21])]), c_0_22]), c_0_46]), c_0_47]), c_0_45]), c_0_84]), c_0_48])).
% 0.37/0.63  cnf(c_0_89, plain, (r3_waybel_9(X1,X2,esk3_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.37/0.63  cnf(c_0_90, plain, (r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.37/0.63  cnf(c_0_91, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,X1,esk3_2(esk6_0,esk7_0)),esk6_0,X1)|v2_struct_0(X1)|~v1_compts_1(esk6_0)|~r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,esk7_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_20]), c_0_21])]), c_0_22])).
% 0.37/0.63  cnf(c_0_92, negated_conjecture, (v1_compts_1(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_20]), c_0_21])]), c_0_22])).
% 0.37/0.63  cnf(c_0_93, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|~v1_compts_1(esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_78]), c_0_20]), c_0_21])]), c_0_22]), c_0_79]), c_0_80]), c_0_81])).
% 0.37/0.63  cnf(c_0_94, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,X1,esk3_2(esk6_0,esk7_0))))|~v1_compts_1(esk6_0)|~r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,esk7_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_86]), c_0_20]), c_0_21])]), c_0_22])).
% 0.37/0.63  cnf(c_0_95, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,X1,esk3_2(esk6_0,esk7_0)),esk6_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,esk7_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])])).
% 0.37/0.63  cnf(c_0_96, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_92])])).
% 0.37/0.63  cnf(c_0_97, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_92])])).
% 0.37/0.63  cnf(c_0_98, negated_conjecture, (v7_waybel_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_92])])).
% 0.37/0.63  cnf(c_0_99, negated_conjecture, (v4_orders_2(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_92])])).
% 0.37/0.63  cnf(c_0_100, negated_conjecture, (~v2_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_92])])).
% 0.37/0.63  cnf(c_0_101, negated_conjecture, (~m2_yellow_6(X1,esk6_0,esk7_0)|~v3_yellow_6(X1,esk6_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.63  fof(c_0_102, plain, ![X19, X20]:(~r2_hidden(X19,X20)|~r1_tarski(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.37/0.63  cnf(c_0_103, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,X1,esk3_2(esk6_0,esk7_0))))|~r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,esk7_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_92])])).
% 0.37/0.63  cnf(c_0_104, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97]), c_0_98]), c_0_99])]), c_0_100])).
% 0.37/0.63  cnf(c_0_105, negated_conjecture, (~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_92])])).
% 0.37/0.63  cnf(c_0_106, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.37/0.63  cnf(c_0_107, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_96]), c_0_97]), c_0_98]), c_0_99])]), c_0_100])).
% 0.37/0.63  cnf(c_0_108, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.37/0.63  cnf(c_0_109, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_104]), c_0_97]), c_0_98]), c_0_99]), c_0_37])]), c_0_100]), c_0_22])).
% 0.37/0.63  cnf(c_0_110, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_104]), c_0_97]), c_0_98]), c_0_99]), c_0_37])]), c_0_100]), c_0_22])).
% 0.37/0.63  cnf(c_0_111, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_104]), c_0_97]), c_0_98]), c_0_99]), c_0_37])]), c_0_100]), c_0_22])).
% 0.37/0.63  cnf(c_0_112, negated_conjecture, (~v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_105, c_0_104])).
% 0.37/0.63  cnf(c_0_113, negated_conjecture, (~v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_104]), c_0_97]), c_0_98]), c_0_99]), c_0_37])]), c_0_100]), c_0_22])).
% 0.37/0.63  cnf(c_0_114, negated_conjecture, (~r1_tarski(k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))),esk3_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.37/0.63  cnf(c_0_115, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110]), c_0_111]), c_0_20]), c_0_21])]), c_0_112]), c_0_113]), c_0_22])).
% 0.37/0.63  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115]), c_0_68])]), ['proof']).
% 0.37/0.63  # SZS output end CNFRefutation
% 0.37/0.63  # Proof object total steps             : 117
% 0.37/0.63  # Proof object clause steps            : 84
% 0.37/0.63  # Proof object formula steps           : 33
% 0.37/0.63  # Proof object conjectures             : 56
% 0.37/0.63  # Proof object clause conjectures      : 53
% 0.37/0.63  # Proof object formula conjectures     : 3
% 0.37/0.63  # Proof object initial clauses used    : 36
% 0.37/0.63  # Proof object initial formulas used   : 16
% 0.37/0.63  # Proof object generating inferences   : 39
% 0.37/0.63  # Proof object simplifying inferences  : 164
% 0.37/0.63  # Training examples: 0 positive, 0 negative
% 0.37/0.63  # Parsed axioms                        : 16
% 0.37/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.63  # Initial clauses                      : 43
% 0.37/0.63  # Removed in clause preprocessing      : 0
% 0.37/0.63  # Initial clauses in saturation        : 43
% 0.37/0.63  # Processed clauses                    : 1839
% 0.37/0.63  # ...of these trivial                  : 3
% 0.37/0.63  # ...subsumed                          : 1050
% 0.37/0.63  # ...remaining for further processing  : 786
% 0.37/0.63  # Other redundant clauses eliminated   : 2
% 0.37/0.63  # Clauses deleted for lack of memory   : 0
% 0.37/0.63  # Backward-subsumed                    : 505
% 0.37/0.63  # Backward-rewritten                   : 33
% 0.37/0.63  # Generated clauses                    : 3792
% 0.37/0.63  # ...of the previous two non-trivial   : 3494
% 0.37/0.63  # Contextual simplify-reflections      : 643
% 0.37/0.63  # Paramodulations                      : 3784
% 0.37/0.63  # Factorizations                       : 6
% 0.37/0.63  # Equation resolutions                 : 2
% 0.37/0.63  # Propositional unsat checks           : 0
% 0.37/0.63  #    Propositional check models        : 0
% 0.37/0.63  #    Propositional check unsatisfiable : 0
% 0.37/0.63  #    Propositional clauses             : 0
% 0.37/0.63  #    Propositional clauses after purity: 0
% 0.37/0.63  #    Propositional unsat core size     : 0
% 0.37/0.63  #    Propositional preprocessing time  : 0.000
% 0.37/0.63  #    Propositional encoding time       : 0.000
% 0.37/0.63  #    Propositional solver time         : 0.000
% 0.37/0.63  #    Success case prop preproc time    : 0.000
% 0.37/0.63  #    Success case prop encoding time   : 0.000
% 0.37/0.63  #    Success case prop solver time     : 0.000
% 0.37/0.63  # Current number of processed clauses  : 204
% 0.37/0.63  #    Positive orientable unit clauses  : 19
% 0.37/0.63  #    Positive unorientable unit clauses: 0
% 0.37/0.63  #    Negative unit clauses             : 4
% 0.37/0.63  #    Non-unit-clauses                  : 181
% 0.37/0.63  # Current number of unprocessed clauses: 1721
% 0.37/0.63  # ...number of literals in the above   : 10159
% 0.37/0.63  # Current number of archived formulas  : 0
% 0.37/0.63  # Current number of archived clauses   : 580
% 0.37/0.63  # Clause-clause subsumption calls (NU) : 321496
% 0.37/0.63  # Rec. Clause-clause subsumption calls : 17890
% 0.37/0.63  # Non-unit clause-clause subsumptions  : 2198
% 0.37/0.63  # Unit Clause-clause subsumption calls : 462
% 0.37/0.63  # Rewrite failures with RHS unbound    : 0
% 0.37/0.63  # BW rewrite match attempts            : 4
% 0.37/0.63  # BW rewrite match successes           : 2
% 0.37/0.63  # Condensation attempts                : 0
% 0.37/0.63  # Condensation successes               : 0
% 0.37/0.63  # Termbank termtop insertions          : 123414
% 0.37/0.63  
% 0.37/0.63  # -------------------------------------------------
% 0.37/0.63  # User time                : 0.266 s
% 0.37/0.63  # System time              : 0.007 s
% 0.37/0.63  # Total time               : 0.273 s
% 0.37/0.63  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
