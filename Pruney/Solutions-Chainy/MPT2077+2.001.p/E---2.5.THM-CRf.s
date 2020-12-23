%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:05 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 (210671 expanded)
%              Number of clauses        :   86 (68906 expanded)
%              Number of leaves         :   15 (52176 expanded)
%              Depth                    :   26
%              Number of atoms          :  689 (2526747 expanded)
%              Number of equality atoms :   13 ( 588 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   44 (   4 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_waybel_9)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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
    ! [X43,X44,X47] :
      ( ( m1_subset_1(esk4_2(X43,X44),u1_struct_0(X43))
        | v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X43)
        | ~ v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( r3_waybel_9(X43,X44,esk4_2(X43,X44))
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
      & ( ~ m1_subset_1(X47,u1_struct_0(X43))
        | ~ r3_waybel_9(X43,esk5_1(X43),X47)
        | v1_compts_1(X43)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).

fof(c_0_17,negated_conjecture,(
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
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

cnf(c_0_18,plain,
    ( l1_waybel_0(esk5_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v4_orders_2(esk5_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v7_waybel_0(esk5_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_25,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_struct_0(X24)
        | ~ m2_yellow_6(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22) )
      & ( v4_orders_2(X24)
        | ~ m2_yellow_6(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22) )
      & ( v7_waybel_0(X24)
        | ~ m2_yellow_6(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22) )
      & ( l1_waybel_0(X24,X22)
        | ~ m2_yellow_6(X24,X22,X23)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_26,negated_conjecture,
    ( m2_yellow_6(esk8_1(X1),esk6_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk6_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | v2_struct_0(X21)
      | ~ v4_orders_2(X21)
      | ~ v7_waybel_0(X21)
      | ~ l1_waybel_0(X21,X20)
      | m1_subset_1(k10_yellow_6(X20,X21),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_32,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_35,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_38,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | m1_subset_1(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])]),c_0_21]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_34])]),c_0_21]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_34])]),c_0_21]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | ~ v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34])]),c_0_21]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_19]),c_0_20])]),c_0_21]),c_0_41]),c_0_42]),c_0_43])).

fof(c_0_46,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_47,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ r3_waybel_9(X31,X32,X33)
        | ~ m1_connsp_2(X34,X31,X33)
        | r2_waybel_0(X31,X32,X34)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_connsp_2(esk2_3(X31,X32,X33),X31,X33)
        | r3_waybel_9(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ r2_waybel_0(X31,X32,esk2_3(X31,X32,X33))
        | r3_waybel_9(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).

cnf(c_0_48,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,plain,
    ( m1_connsp_2(esk2_3(X1,X2,X3),X1,X3)
    | r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_52,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ v4_orders_2(X37)
      | ~ v7_waybel_0(X37)
      | ~ l1_waybel_0(X37,X36)
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | ~ r2_hidden(X38,k10_yellow_6(X36,X37))
      | r3_waybel_9(X36,X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

cnf(c_0_53,plain,
    ( r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_connsp_2(X4,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | m1_connsp_2(esk2_3(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2)),esk6_0,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))
    | r3_waybel_9(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2)
    | ~ l1_waybel_0(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_55,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r2_waybel_0(esk6_0,X1,X2)
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X3)
    | ~ m1_connsp_2(X2,esk6_0,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X3))
    | ~ r3_waybel_9(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X3))
    | ~ l1_waybel_0(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_51]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | m1_connsp_2(esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)),esk6_0,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_27])).

cnf(c_0_58,plain,
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
    inference(spm,[status(thm)],[c_0_55,c_0_49])).

fof(c_0_59,plain,(
    ! [X25,X26,X27,X28] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | v2_struct_0(X26)
      | ~ v4_orders_2(X26)
      | ~ v7_waybel_0(X26)
      | ~ l1_waybel_0(X26,X25)
      | ~ m2_yellow_6(X27,X25,X26)
      | ~ r2_waybel_0(X25,X27,X28)
      | r2_waybel_0(X25,X26,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

cnf(c_0_60,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | r2_waybel_0(esk6_0,X2,esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(X2)
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)
    | ~ r3_waybel_9(esk6_0,X2,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | ~ l1_waybel_0(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_19]),c_0_20])]),c_0_21]),c_0_41]),c_0_42]),c_0_40]),c_0_43])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | r2_waybel_0(esk6_0,esk8_1(esk5_1(esk6_0)),esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_40]),c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | r2_waybel_0(esk6_0,X2,esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(X2)
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,X2)
    | ~ l1_waybel_0(X2,esk6_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_34])]),c_0_21])).

fof(c_0_65,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_66,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_67,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,esk2_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_68,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | r2_waybel_0(esk6_0,esk5_1(esk6_0),esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_33]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk5_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_72,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_19]),c_0_20])]),c_0_21]),c_0_51]),c_0_27])).

fof(c_0_73,plain,(
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

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_19]),c_0_20])]),c_0_21]),c_0_51])).

cnf(c_0_76,negated_conjecture,
    ( v3_yellow_6(esk8_1(X1),esk6_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk6_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_77,plain,(
    ! [X39,X40,X41] :
      ( ( m2_yellow_6(esk3_3(X39,X40,X41),X39,X40)
        | ~ r3_waybel_9(X39,X40,X41)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | v2_struct_0(X40)
        | ~ v4_orders_2(X40)
        | ~ v7_waybel_0(X40)
        | ~ l1_waybel_0(X40,X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( r2_hidden(X41,k10_yellow_6(X39,esk3_3(X39,X40,X41)))
        | ~ r3_waybel_9(X39,X40,X41)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | v2_struct_0(X40)
        | ~ v4_orders_2(X40)
        | ~ v7_waybel_0(X40)
        | ~ l1_waybel_0(X40,X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_78,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_79,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_80,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_81,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_82,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_86,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk4_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v1_compts_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_19]),c_0_20])]),c_0_21]),c_0_80]),c_0_81]),c_0_82])).

cnf(c_0_88,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk5_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_89,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_19]),c_0_20])]),c_0_21]),c_0_41]),c_0_42]),c_0_40]),c_0_85]),c_0_43])).

cnf(c_0_90,plain,
    ( r3_waybel_9(X1,X2,esk4_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_91,negated_conjecture,
    ( m2_yellow_6(esk3_3(esk6_0,X1,esk4_2(esk6_0,esk7_0)),esk6_0,X1)
    | v2_struct_0(X1)
    | ~ v1_compts_1(esk6_0)
    | ~ r3_waybel_9(esk6_0,X1,esk4_2(esk6_0,esk7_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_92,negated_conjecture,
    ( v1_compts_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_93,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0))
    | ~ v1_compts_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_79]),c_0_19]),c_0_20])]),c_0_21]),c_0_80]),c_0_81]),c_0_82])).

cnf(c_0_94,negated_conjecture,
    ( m2_yellow_6(esk3_3(esk6_0,X1,esk4_2(esk6_0,esk7_0)),esk6_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk6_0,X1,esk4_2(esk6_0,esk7_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_95,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_92])])).

cnf(c_0_96,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_92])])).

cnf(c_0_97,negated_conjecture,
    ( v7_waybel_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_92])])).

cnf(c_0_98,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_92])])).

cnf(c_0_99,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_92])])).

cnf(c_0_100,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_101,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_102,negated_conjecture,
    ( m2_yellow_6(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_97]),c_0_98])]),c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_92])])).

cnf(c_0_104,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk4_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk3_3(esk6_0,X1,esk4_2(esk6_0,esk7_0))))
    | ~ v1_compts_1(esk6_0)
    | ~ r3_waybel_9(esk6_0,X1,esk4_2(esk6_0,esk7_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_87]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_105,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_106,negated_conjecture,
    ( l1_waybel_0(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_102]),c_0_96]),c_0_97]),c_0_98]),c_0_34])]),c_0_99]),c_0_21])).

cnf(c_0_107,negated_conjecture,
    ( v7_waybel_0(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_102]),c_0_96]),c_0_97]),c_0_98]),c_0_34])]),c_0_99]),c_0_21])).

cnf(c_0_108,negated_conjecture,
    ( v4_orders_2(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_102]),c_0_96]),c_0_97]),c_0_98]),c_0_34])]),c_0_99]),c_0_21])).

cnf(c_0_109,negated_conjecture,
    ( ~ v3_yellow_6(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( ~ v2_struct_0(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_102]),c_0_96]),c_0_97]),c_0_98]),c_0_34])]),c_0_99]),c_0_21])).

fof(c_0_111,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ r1_tarski(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_112,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk4_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk3_3(esk6_0,X1,esk4_2(esk6_0,esk7_0))))
    | ~ r3_waybel_9(esk6_0,X1,esk4_2(esk6_0,esk7_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_92])])).

cnf(c_0_113,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_108]),c_0_19]),c_0_20])]),c_0_109]),c_0_110]),c_0_21])).

cnf(c_0_114,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk7_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_95]),c_0_96]),c_0_97]),c_0_98])]),c_0_99]),c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:03:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.033 s
% 0.21/0.44  # Presaturation interreduction done
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow19)).
% 0.21/0.44  fof(t35_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_yellow19)).
% 0.21/0.44  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.44  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.21/0.44  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.21/0.44  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.44  fof(d9_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>![X4]:(m1_connsp_2(X4,X1,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_waybel_9)).
% 0.21/0.44  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.21/0.44  fof(t27_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(r2_waybel_0(X1,X3,X4)=>r2_waybel_0(X1,X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_6)).
% 0.21/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.44  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.21/0.44  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.21/0.44  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.44  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.21/0.44  fof(c_0_16, plain, ![X43, X44, X47]:(((m1_subset_1(esk4_2(X43,X44),u1_struct_0(X43))|(v2_struct_0(X44)|~v4_orders_2(X44)|~v7_waybel_0(X44)|~l1_waybel_0(X44,X43))|~v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))&(r3_waybel_9(X43,X44,esk4_2(X43,X44))|(v2_struct_0(X44)|~v4_orders_2(X44)|~v7_waybel_0(X44)|~l1_waybel_0(X44,X43))|~v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(((((~v2_struct_0(esk5_1(X43))|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))&(v4_orders_2(esk5_1(X43))|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(v7_waybel_0(esk5_1(X43))|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(l1_waybel_0(esk5_1(X43),X43)|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(~m1_subset_1(X47,u1_struct_0(X43))|~r3_waybel_9(X43,esk5_1(X43),X47)|v1_compts_1(X43)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).
% 0.21/0.44  fof(c_0_17, negated_conjecture, ![X50, X51]:(((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&((((((~v2_struct_0(esk7_0)|~v1_compts_1(esk6_0))&(v4_orders_2(esk7_0)|~v1_compts_1(esk6_0)))&(v7_waybel_0(esk7_0)|~v1_compts_1(esk6_0)))&(l1_waybel_0(esk7_0,esk6_0)|~v1_compts_1(esk6_0)))&(~m2_yellow_6(X50,esk6_0,esk7_0)|~v3_yellow_6(X50,esk6_0)|~v1_compts_1(esk6_0)))&((m2_yellow_6(esk8_1(X51),esk6_0,X51)|(v2_struct_0(X51)|~v4_orders_2(X51)|~v7_waybel_0(X51)|~l1_waybel_0(X51,esk6_0))|v1_compts_1(esk6_0))&(v3_yellow_6(esk8_1(X51),esk6_0)|(v2_struct_0(X51)|~v4_orders_2(X51)|~v7_waybel_0(X51)|~l1_waybel_0(X51,esk6_0))|v1_compts_1(esk6_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.21/0.44  cnf(c_0_18, plain, (l1_waybel_0(esk5_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_22, plain, (v4_orders_2(esk5_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_23, plain, (v7_waybel_0(esk5_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  fof(c_0_24, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.44  fof(c_0_25, plain, ![X22, X23, X24]:((((~v2_struct_0(X24)|~m2_yellow_6(X24,X22,X23)|(v2_struct_0(X22)|~l1_struct_0(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22)))&(v4_orders_2(X24)|~m2_yellow_6(X24,X22,X23)|(v2_struct_0(X22)|~l1_struct_0(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22))))&(v7_waybel_0(X24)|~m2_yellow_6(X24,X22,X23)|(v2_struct_0(X22)|~l1_struct_0(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22))))&(l1_waybel_0(X24,X22)|~m2_yellow_6(X24,X22,X23)|(v2_struct_0(X22)|~l1_struct_0(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.21/0.44  cnf(c_0_26, negated_conjecture, (m2_yellow_6(esk8_1(X1),esk6_0,X1)|v2_struct_0(X1)|v1_compts_1(esk6_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_27, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), c_0_21])).
% 0.21/0.44  cnf(c_0_28, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_20])]), c_0_21])).
% 0.21/0.44  cnf(c_0_29, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_20])]), c_0_21])).
% 0.21/0.44  cnf(c_0_30, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.44  fof(c_0_31, plain, ![X20, X21]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20)|m1_subset_1(k10_yellow_6(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.21/0.44  cnf(c_0_32, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.44  cnf(c_0_33, negated_conjecture, (v1_compts_1(esk6_0)|m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.21/0.44  cnf(c_0_34, negated_conjecture, (l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.21/0.44  cnf(c_0_35, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.44  cnf(c_0_36, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.44  cnf(c_0_37, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.44  fof(c_0_38, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|m1_subset_1(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.44  cnf(c_0_39, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.44  cnf(c_0_40, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])]), c_0_21]), c_0_28]), c_0_29]), c_0_27])).
% 0.21/0.44  cnf(c_0_41, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_33]), c_0_34])]), c_0_21]), c_0_28]), c_0_29]), c_0_27])).
% 0.21/0.44  cnf(c_0_42, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_34])]), c_0_21]), c_0_28]), c_0_29]), c_0_27])).
% 0.21/0.44  cnf(c_0_43, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|~v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_34])]), c_0_21]), c_0_28]), c_0_29]), c_0_27])).
% 0.21/0.44  cnf(c_0_44, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.44  cnf(c_0_45, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_19]), c_0_20])]), c_0_21]), c_0_41]), c_0_42]), c_0_43])).
% 0.21/0.44  fof(c_0_46, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.44  fof(c_0_47, plain, ![X31, X32, X33, X34]:((~r3_waybel_9(X31,X32,X33)|(~m1_connsp_2(X34,X31,X33)|r2_waybel_0(X31,X32,X34))|~m1_subset_1(X33,u1_struct_0(X31))|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&((m1_connsp_2(esk2_3(X31,X32,X33),X31,X33)|r3_waybel_9(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(~r2_waybel_0(X31,X32,esk2_3(X31,X32,X33))|r3_waybel_9(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).
% 0.21/0.44  cnf(c_0_48, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.44  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.44  cnf(c_0_50, plain, (m1_connsp_2(esk2_3(X1,X2,X3),X1,X3)|r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.44  cnf(c_0_51, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.44  fof(c_0_52, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(v2_struct_0(X37)|~v4_orders_2(X37)|~v7_waybel_0(X37)|~l1_waybel_0(X37,X36)|(~m1_subset_1(X38,u1_struct_0(X36))|(~r2_hidden(X38,k10_yellow_6(X36,X37))|r3_waybel_9(X36,X37,X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.21/0.44  cnf(c_0_53, plain, (r2_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_connsp_2(X4,X1,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.44  cnf(c_0_54, negated_conjecture, (v1_compts_1(esk6_0)|m1_connsp_2(esk2_3(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2)),esk6_0,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))|r3_waybel_9(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X2)|~l1_waybel_0(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_19]), c_0_20])]), c_0_21])).
% 0.21/0.44  cnf(c_0_55, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.44  cnf(c_0_56, negated_conjecture, (v1_compts_1(esk6_0)|r2_waybel_0(esk6_0,X1,X2)|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X3)|~m1_connsp_2(X2,esk6_0,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X3))|~r3_waybel_9(esk6_0,X1,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X3))|~l1_waybel_0(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_51]), c_0_19]), c_0_20])]), c_0_21])).
% 0.21/0.44  cnf(c_0_57, negated_conjecture, (v1_compts_1(esk6_0)|m1_connsp_2(esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)),esk6_0,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(spm,[status(thm)],[c_0_54, c_0_27])).
% 0.21/0.44  cnf(c_0_58, plain, (r3_waybel_9(X1,X2,esk1_2(k10_yellow_6(X1,X2),X3))|v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(k10_yellow_6(X1,X2),X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(k10_yellow_6(X1,X2),X3),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_55, c_0_49])).
% 0.21/0.44  fof(c_0_59, plain, ![X25, X26, X27, X28]:(v2_struct_0(X25)|~l1_struct_0(X25)|(v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25)|(~m2_yellow_6(X27,X25,X26)|(~r2_waybel_0(X25,X27,X28)|r2_waybel_0(X25,X26,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).
% 0.21/0.44  cnf(c_0_60, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|r2_waybel_0(esk6_0,X2,esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(X2)|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)|~r3_waybel_9(esk6_0,X2,esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|~l1_waybel_0(X2,esk6_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.44  cnf(c_0_61, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_51]), c_0_19]), c_0_20])]), c_0_21]), c_0_41]), c_0_42]), c_0_40]), c_0_43])).
% 0.21/0.44  cnf(c_0_62, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_waybel_0(X1,X2,X4)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~r2_waybel_0(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.44  cnf(c_0_63, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|r2_waybel_0(esk6_0,esk8_1(esk5_1(esk6_0)),esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_40]), c_0_43])).
% 0.21/0.44  cnf(c_0_64, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|r2_waybel_0(esk6_0,X2,esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(X2)|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,X2)|~l1_waybel_0(X2,esk6_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_34])]), c_0_21])).
% 0.21/0.44  fof(c_0_65, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.44  fof(c_0_66, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.44  cnf(c_0_67, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_0(X1,X2,esk2_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.44  cnf(c_0_68, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|r2_waybel_0(esk6_0,esk5_1(esk6_0),esk2_3(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_33]), c_0_28]), c_0_29]), c_0_27])).
% 0.21/0.44  cnf(c_0_69, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.44  cnf(c_0_70, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.44  cnf(c_0_71, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk5_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_72, negated_conjecture, (v1_compts_1(esk6_0)|r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_2(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_19]), c_0_20])]), c_0_21]), c_0_51]), c_0_27])).
% 0.21/0.44  fof(c_0_73, plain, ![X29, X30]:((~v3_yellow_6(X30,X29)|k10_yellow_6(X29,X30)!=k1_xboole_0|(v2_struct_0(X30)|~v4_orders_2(X30)|~v7_waybel_0(X30)|~l1_waybel_0(X30,X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(k10_yellow_6(X29,X30)=k1_xboole_0|v3_yellow_6(X30,X29)|(v2_struct_0(X30)|~v4_orders_2(X30)|~v7_waybel_0(X30)|~l1_waybel_0(X30,X29))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.21/0.44  cnf(c_0_74, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.21/0.44  cnf(c_0_75, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_19]), c_0_20])]), c_0_21]), c_0_51])).
% 0.21/0.44  cnf(c_0_76, negated_conjecture, (v3_yellow_6(esk8_1(X1),esk6_0)|v2_struct_0(X1)|v1_compts_1(esk6_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  fof(c_0_77, plain, ![X39, X40, X41]:((m2_yellow_6(esk3_3(X39,X40,X41),X39,X40)|~r3_waybel_9(X39,X40,X41)|~m1_subset_1(X41,u1_struct_0(X39))|(v2_struct_0(X40)|~v4_orders_2(X40)|~v7_waybel_0(X40)|~l1_waybel_0(X40,X39))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(r2_hidden(X41,k10_yellow_6(X39,esk3_3(X39,X40,X41)))|~r3_waybel_9(X39,X40,X41)|~m1_subset_1(X41,u1_struct_0(X39))|(v2_struct_0(X40)|~v4_orders_2(X40)|~v7_waybel_0(X40)|~l1_waybel_0(X40,X39))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.21/0.44  cnf(c_0_78, plain, (m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_79, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_80, negated_conjecture, (v4_orders_2(esk7_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_81, negated_conjecture, (v7_waybel_0(esk7_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_82, negated_conjecture, (~v2_struct_0(esk7_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_83, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.21/0.44  cnf(c_0_84, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.21/0.44  cnf(c_0_85, negated_conjecture, (v1_compts_1(esk6_0)|v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_27]), c_0_28]), c_0_29])).
% 0.21/0.44  cnf(c_0_86, plain, (m2_yellow_6(esk3_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.21/0.44  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk4_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~v1_compts_1(esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_19]), c_0_20])]), c_0_21]), c_0_80]), c_0_81]), c_0_82])).
% 0.21/0.44  cnf(c_0_88, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk5_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_89, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_19]), c_0_20])]), c_0_21]), c_0_41]), c_0_42]), c_0_40]), c_0_85]), c_0_43])).
% 0.21/0.44  cnf(c_0_90, plain, (r3_waybel_9(X1,X2,esk4_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_91, negated_conjecture, (m2_yellow_6(esk3_3(esk6_0,X1,esk4_2(esk6_0,esk7_0)),esk6_0,X1)|v2_struct_0(X1)|~v1_compts_1(esk6_0)|~r3_waybel_9(esk6_0,X1,esk4_2(esk6_0,esk7_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_19]), c_0_20])]), c_0_21])).
% 0.21/0.44  cnf(c_0_92, negated_conjecture, (v1_compts_1(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_19]), c_0_20])]), c_0_21])).
% 0.21/0.44  cnf(c_0_93, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0))|~v1_compts_1(esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_79]), c_0_19]), c_0_20])]), c_0_21]), c_0_80]), c_0_81]), c_0_82])).
% 0.21/0.44  cnf(c_0_94, negated_conjecture, (m2_yellow_6(esk3_3(esk6_0,X1,esk4_2(esk6_0,esk7_0)),esk6_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk6_0,X1,esk4_2(esk6_0,esk7_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])])).
% 0.21/0.44  cnf(c_0_95, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_92])])).
% 0.21/0.44  cnf(c_0_96, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_92])])).
% 0.21/0.44  cnf(c_0_97, negated_conjecture, (v7_waybel_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_92])])).
% 0.21/0.44  cnf(c_0_98, negated_conjecture, (v4_orders_2(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_92])])).
% 0.21/0.44  cnf(c_0_99, negated_conjecture, (~v2_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_92])])).
% 0.21/0.44  cnf(c_0_100, negated_conjecture, (~m2_yellow_6(X1,esk6_0,esk7_0)|~v3_yellow_6(X1,esk6_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_101, plain, (r2_hidden(X1,k10_yellow_6(X2,esk3_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.21/0.44  cnf(c_0_102, negated_conjecture, (m2_yellow_6(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_97]), c_0_98])]), c_0_99])).
% 0.21/0.44  cnf(c_0_103, negated_conjecture, (~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_92])])).
% 0.21/0.44  cnf(c_0_104, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk4_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk3_3(esk6_0,X1,esk4_2(esk6_0,esk7_0))))|~v1_compts_1(esk6_0)|~r3_waybel_9(esk6_0,X1,esk4_2(esk6_0,esk7_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_87]), c_0_19]), c_0_20])]), c_0_21])).
% 0.21/0.44  cnf(c_0_105, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.21/0.44  cnf(c_0_106, negated_conjecture, (l1_waybel_0(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)),esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_102]), c_0_96]), c_0_97]), c_0_98]), c_0_34])]), c_0_99]), c_0_21])).
% 0.21/0.44  cnf(c_0_107, negated_conjecture, (v7_waybel_0(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_102]), c_0_96]), c_0_97]), c_0_98]), c_0_34])]), c_0_99]), c_0_21])).
% 0.21/0.44  cnf(c_0_108, negated_conjecture, (v4_orders_2(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_102]), c_0_96]), c_0_97]), c_0_98]), c_0_34])]), c_0_99]), c_0_21])).
% 0.21/0.44  cnf(c_0_109, negated_conjecture, (~v3_yellow_6(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_103, c_0_102])).
% 0.21/0.44  cnf(c_0_110, negated_conjecture, (~v2_struct_0(esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_102]), c_0_96]), c_0_97]), c_0_98]), c_0_34])]), c_0_99]), c_0_21])).
% 0.21/0.44  fof(c_0_111, plain, ![X17, X18]:(~r2_hidden(X17,X18)|~r1_tarski(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.44  cnf(c_0_112, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk4_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk3_3(esk6_0,X1,esk4_2(esk6_0,esk7_0))))|~r3_waybel_9(esk6_0,X1,esk4_2(esk6_0,esk7_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_92])])).
% 0.21/0.44  cnf(c_0_113, negated_conjecture, (k10_yellow_6(esk6_0,esk3_3(esk6_0,esk7_0,esk4_2(esk6_0,esk7_0)))=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107]), c_0_108]), c_0_19]), c_0_20])]), c_0_109]), c_0_110]), c_0_21])).
% 0.21/0.44  cnf(c_0_114, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.21/0.44  cnf(c_0_115, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk7_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_95]), c_0_96]), c_0_97]), c_0_98])]), c_0_99]), c_0_113])).
% 0.21/0.44  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_70])]), ['proof']).
% 0.21/0.44  # SZS output end CNFRefutation
% 0.21/0.44  # Proof object total steps             : 117
% 0.21/0.44  # Proof object clause steps            : 86
% 0.21/0.44  # Proof object formula steps           : 31
% 0.21/0.44  # Proof object conjectures             : 60
% 0.21/0.44  # Proof object clause conjectures      : 57
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 37
% 0.21/0.44  # Proof object initial formulas used   : 15
% 0.21/0.44  # Proof object generating inferences   : 41
% 0.21/0.44  # Proof object simplifying inferences  : 179
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 15
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 41
% 0.21/0.44  # Removed in clause preprocessing      : 0
% 0.21/0.44  # Initial clauses in saturation        : 41
% 0.21/0.44  # Processed clauses                    : 321
% 0.21/0.44  # ...of these trivial                  : 3
% 0.21/0.44  # ...subsumed                          : 26
% 0.21/0.44  # ...remaining for further processing  : 292
% 0.21/0.44  # Other redundant clauses eliminated   : 2
% 0.21/0.44  # Clauses deleted for lack of memory   : 0
% 0.21/0.44  # Backward-subsumed                    : 166
% 0.21/0.44  # Backward-rewritten                   : 21
% 0.21/0.44  # Generated clauses                    : 417
% 0.21/0.44  # ...of the previous two non-trivial   : 381
% 0.21/0.44  # Contextual simplify-reflections      : 391
% 0.21/0.44  # Paramodulations                      : 415
% 0.21/0.44  # Factorizations                       : 0
% 0.21/0.44  # Equation resolutions                 : 2
% 0.21/0.44  # Propositional unsat checks           : 0
% 0.21/0.44  #    Propositional check models        : 0
% 0.21/0.44  #    Propositional check unsatisfiable : 0
% 0.21/0.44  #    Propositional clauses             : 0
% 0.21/0.44  #    Propositional clauses after purity: 0
% 0.21/0.44  #    Propositional unsat core size     : 0
% 0.21/0.44  #    Propositional preprocessing time  : 0.000
% 0.21/0.44  #    Propositional encoding time       : 0.000
% 0.21/0.44  #    Propositional solver time         : 0.000
% 0.21/0.44  #    Success case prop preproc time    : 0.000
% 0.21/0.44  #    Success case prop encoding time   : 0.000
% 0.21/0.44  #    Success case prop solver time     : 0.000
% 0.21/0.44  # Current number of processed clauses  : 63
% 0.21/0.44  #    Positive orientable unit clauses  : 19
% 0.21/0.44  #    Positive unorientable unit clauses: 0
% 0.21/0.44  #    Negative unit clauses             : 4
% 0.21/0.44  #    Non-unit-clauses                  : 40
% 0.21/0.44  # Current number of unprocessed clauses: 129
% 0.21/0.44  # ...number of literals in the above   : 834
% 0.21/0.44  # Current number of archived formulas  : 0
% 0.21/0.44  # Current number of archived clauses   : 227
% 0.21/0.44  # Clause-clause subsumption calls (NU) : 41390
% 0.21/0.44  # Rec. Clause-clause subsumption calls : 1119
% 0.21/0.44  # Non-unit clause-clause subsumptions  : 582
% 0.21/0.44  # Unit Clause-clause subsumption calls : 17
% 0.21/0.44  # Rewrite failures with RHS unbound    : 0
% 0.21/0.44  # BW rewrite match attempts            : 4
% 0.21/0.44  # BW rewrite match successes           : 1
% 0.21/0.44  # Condensation attempts                : 0
% 0.21/0.44  # Condensation successes               : 0
% 0.21/0.44  # Termbank termtop insertions          : 30679
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.090 s
% 0.21/0.44  # System time              : 0.006 s
% 0.21/0.44  # Total time               : 0.096 s
% 0.21/0.44  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
