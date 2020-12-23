%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:06 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 (141772 expanded)
%              Number of clauses        :   79 (46329 expanded)
%              Number of leaves         :   14 (35110 expanded)
%              Depth                    :   21
%              Number of atoms          :  608 (1702545 expanded)
%              Number of equality atoms :   13 ( 588 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   44 (   4 average)
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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X38,X39,X42] :
      ( ( m1_subset_1(esk3_2(X38,X39),u1_struct_0(X38))
        | v2_struct_0(X39)
        | ~ v4_orders_2(X39)
        | ~ v7_waybel_0(X39)
        | ~ l1_waybel_0(X39,X38)
        | ~ v1_compts_1(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r3_waybel_9(X38,X39,esk3_2(X38,X39))
        | v2_struct_0(X39)
        | ~ v4_orders_2(X39)
        | ~ v7_waybel_0(X39)
        | ~ l1_waybel_0(X39,X38)
        | ~ v1_compts_1(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ v2_struct_0(esk4_1(X38))
        | v1_compts_1(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( v4_orders_2(esk4_1(X38))
        | v1_compts_1(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( v7_waybel_0(esk4_1(X38))
        | v1_compts_1(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( l1_waybel_0(esk4_1(X38),X38)
        | v1_compts_1(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ m1_subset_1(X42,u1_struct_0(X38))
        | ~ r3_waybel_9(X38,esk4_1(X38),X42)
        | v1_compts_1(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X45,X46] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & l1_pre_topc(esk5_0)
      & ( ~ v2_struct_0(esk6_0)
        | ~ v1_compts_1(esk5_0) )
      & ( v4_orders_2(esk6_0)
        | ~ v1_compts_1(esk5_0) )
      & ( v7_waybel_0(esk6_0)
        | ~ v1_compts_1(esk5_0) )
      & ( l1_waybel_0(esk6_0,esk5_0)
        | ~ v1_compts_1(esk5_0) )
      & ( ~ m2_yellow_6(X45,esk5_0,esk6_0)
        | ~ v3_yellow_6(X45,esk5_0)
        | ~ v1_compts_1(esk5_0) )
      & ( m2_yellow_6(esk7_1(X46),esk5_0,X46)
        | v2_struct_0(X46)
        | ~ v4_orders_2(X46)
        | ~ v7_waybel_0(X46)
        | ~ l1_waybel_0(X46,esk5_0)
        | v1_compts_1(esk5_0) )
      & ( v3_yellow_6(esk7_1(X46),esk5_0)
        | v2_struct_0(X46)
        | ~ v4_orders_2(X46)
        | ~ v7_waybel_0(X46)
        | ~ l1_waybel_0(X46,esk5_0)
        | v1_compts_1(esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).

cnf(c_0_17,plain,
    ( l1_waybel_0(esk4_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v4_orders_2(esk4_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v7_waybel_0(esk4_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_24,plain,(
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

cnf(c_0_25,negated_conjecture,
    ( m2_yellow_6(esk7_1(X1),esk5_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk5_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | l1_waybel_0(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v7_waybel_0(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
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

cnf(c_0_31,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | m2_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0,esk4_1(esk5_0))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_34,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | m1_subset_1(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | l1_waybel_0(esk7_1(esk4_1(esk5_0)),esk5_0)
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_20]),c_0_27]),c_0_28]),c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v4_orders_2(esk7_1(esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_33])]),c_0_20]),c_0_27]),c_0_28]),c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v7_waybel_0(esk7_1(esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_33])]),c_0_20]),c_0_27]),c_0_28]),c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v2_struct_0(esk7_1(esk4_1(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_33])]),c_0_20]),c_0_27]),c_0_28]),c_0_26])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_18]),c_0_19])]),c_0_20]),c_0_40]),c_0_41]),c_0_42])).

fof(c_0_45,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_46,plain,(
    ! [X27,X28,X29] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ v4_orders_2(X28)
      | ~ v7_waybel_0(X28)
      | ~ l1_waybel_0(X28,X27)
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | ~ r2_hidden(X29,k10_yellow_6(X27,X28))
      | r3_waybel_9(X27,X28,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

fof(c_0_47,plain,(
    ! [X30,X31,X32,X33] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v4_orders_2(X31)
      | ~ v7_waybel_0(X31)
      | ~ l1_waybel_0(X31,X30)
      | ~ m2_yellow_6(X32,X30,X31)
      | ~ m1_subset_1(X33,u1_struct_0(X30))
      | ~ r3_waybel_9(X30,X32,X33)
      | r3_waybel_9(X30,X31,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

cnf(c_0_48,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1),u1_struct_0(esk5_0))
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
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
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | r3_waybel_9(esk5_0,X1,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2)
    | ~ r3_waybel_9(esk5_0,X3,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))
    | ~ m2_yellow_6(X3,esk5_0,X1)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | r3_waybel_9(esk5_0,esk7_1(esk4_1(esk5_0)),esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1))
    | v2_struct_0(esk4_1(esk5_0))
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_18]),c_0_19])]),c_0_20]),c_0_40]),c_0_41]),c_0_39]),c_0_42])).

fof(c_0_56,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_57,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_58,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | r3_waybel_9(esk5_0,X1,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2)
    | ~ m2_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0,X1)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk4_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | r3_waybel_9(esk5_0,esk4_1(esk5_0),esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1))
    | v2_struct_0(esk4_1(esk5_0))
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_32]),c_0_27]),c_0_28]),c_0_26])).

fof(c_0_63,plain,(
    ! [X25,X26] :
      ( ( ~ v3_yellow_6(X26,X25)
        | k10_yellow_6(X25,X26) != k1_xboole_0
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( k10_yellow_6(X25,X26) = k1_xboole_0
        | v3_yellow_6(X26,X25)
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_18]),c_0_19])]),c_0_20]),c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( v3_yellow_6(esk7_1(X1),esk5_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk5_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_67,plain,(
    ! [X34,X35,X36] :
      ( ( m2_yellow_6(esk2_3(X34,X35,X36),X34,X35)
        | ~ r3_waybel_9(X34,X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | v2_struct_0(X35)
        | ~ v4_orders_2(X35)
        | ~ v7_waybel_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(X36,k10_yellow_6(X34,esk2_3(X34,X35,X36)))
        | ~ r3_waybel_9(X34,X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | v2_struct_0(X35)
        | ~ v4_orders_2(X35)
        | ~ v7_waybel_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_68,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_70,negated_conjecture,
    ( v4_orders_2(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_71,negated_conjecture,
    ( v7_waybel_0(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_72,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))) = k1_xboole_0
    | v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v3_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0)
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_76,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ v1_compts_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_18]),c_0_19])]),c_0_20]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_78,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk4_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_79,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_18]),c_0_19])]),c_0_20]),c_0_40]),c_0_41]),c_0_39]),c_0_75]),c_0_42])).

cnf(c_0_80,plain,
    ( r3_waybel_9(X1,X2,esk3_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_81,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0)),esk5_0,X1)
    | v2_struct_0(X1)
    | ~ v1_compts_1(esk5_0)
    | ~ r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_83,negated_conjecture,
    ( v1_compts_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_84,negated_conjecture,
    ( r3_waybel_9(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))
    | ~ v1_compts_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_69]),c_0_18]),c_0_19])]),c_0_20]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0))))
    | ~ v1_compts_1(esk5_0)
    | ~ r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_77]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_86,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0)),esk5_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_87,negated_conjecture,
    ( r3_waybel_9(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_83])])).

cnf(c_0_88,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_83])])).

cnf(c_0_89,negated_conjecture,
    ( v7_waybel_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_83])])).

cnf(c_0_90,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_83])])).

cnf(c_0_91,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_83])])).

cnf(c_0_92,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk5_0,esk6_0)
    | ~ v3_yellow_6(X1,esk5_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_93,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ r1_tarski(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_94,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0))))
    | ~ r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_83])])).

cnf(c_0_95,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_89]),c_0_90])]),c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( ~ v3_yellow_6(X1,esk5_0)
    | ~ m2_yellow_6(X1,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_83])])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_87]),c_0_88]),c_0_89]),c_0_90])]),c_0_91])).

cnf(c_0_99,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_100,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_95]),c_0_88]),c_0_89]),c_0_90]),c_0_33])]),c_0_91]),c_0_20])).

cnf(c_0_101,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_95]),c_0_88]),c_0_89]),c_0_90]),c_0_33])]),c_0_91]),c_0_20])).

cnf(c_0_102,negated_conjecture,
    ( v4_orders_2(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_95]),c_0_88]),c_0_89]),c_0_90]),c_0_33])]),c_0_91]),c_0_20])).

cnf(c_0_103,negated_conjecture,
    ( ~ v3_yellow_6(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( ~ v2_struct_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_95]),c_0_88]),c_0_89]),c_0_90]),c_0_33])]),c_0_91]),c_0_20])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_tarski(k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))),esk3_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101]),c_0_102]),c_0_18]),c_0_19])]),c_0_103]),c_0_104]),c_0_20])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.043 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 0.20/0.42  fof(t35_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_yellow19)).
% 0.20/0.42  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.42  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.20/0.42  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.20/0.42  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.42  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.20/0.42  fof(t31_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 0.20/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.42  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.20/0.42  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.20/0.42  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.42  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.20/0.42  fof(c_0_15, plain, ![X38, X39, X42]:(((m1_subset_1(esk3_2(X38,X39),u1_struct_0(X38))|(v2_struct_0(X39)|~v4_orders_2(X39)|~v7_waybel_0(X39)|~l1_waybel_0(X39,X38))|~v1_compts_1(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(r3_waybel_9(X38,X39,esk3_2(X38,X39))|(v2_struct_0(X39)|~v4_orders_2(X39)|~v7_waybel_0(X39)|~l1_waybel_0(X39,X38))|~v1_compts_1(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))&(((((~v2_struct_0(esk4_1(X38))|v1_compts_1(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(v4_orders_2(esk4_1(X38))|v1_compts_1(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))&(v7_waybel_0(esk4_1(X38))|v1_compts_1(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))&(l1_waybel_0(esk4_1(X38),X38)|v1_compts_1(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))&(~m1_subset_1(X42,u1_struct_0(X38))|~r3_waybel_9(X38,esk4_1(X38),X42)|v1_compts_1(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).
% 0.20/0.42  fof(c_0_16, negated_conjecture, ![X45, X46]:(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((((((~v2_struct_0(esk6_0)|~v1_compts_1(esk5_0))&(v4_orders_2(esk6_0)|~v1_compts_1(esk5_0)))&(v7_waybel_0(esk6_0)|~v1_compts_1(esk5_0)))&(l1_waybel_0(esk6_0,esk5_0)|~v1_compts_1(esk5_0)))&(~m2_yellow_6(X45,esk5_0,esk6_0)|~v3_yellow_6(X45,esk5_0)|~v1_compts_1(esk5_0)))&((m2_yellow_6(esk7_1(X46),esk5_0,X46)|(v2_struct_0(X46)|~v4_orders_2(X46)|~v7_waybel_0(X46)|~l1_waybel_0(X46,esk5_0))|v1_compts_1(esk5_0))&(v3_yellow_6(esk7_1(X46),esk5_0)|(v2_struct_0(X46)|~v4_orders_2(X46)|~v7_waybel_0(X46)|~l1_waybel_0(X46,esk5_0))|v1_compts_1(esk5_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).
% 0.20/0.42  cnf(c_0_17, plain, (l1_waybel_0(esk4_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_21, plain, (v4_orders_2(esk4_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_22, plain, (v7_waybel_0(esk4_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  fof(c_0_23, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.42  fof(c_0_24, plain, ![X22, X23, X24]:((((~v2_struct_0(X24)|~m2_yellow_6(X24,X22,X23)|(v2_struct_0(X22)|~l1_struct_0(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22)))&(v4_orders_2(X24)|~m2_yellow_6(X24,X22,X23)|(v2_struct_0(X22)|~l1_struct_0(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22))))&(v7_waybel_0(X24)|~m2_yellow_6(X24,X22,X23)|(v2_struct_0(X22)|~l1_struct_0(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22))))&(l1_waybel_0(X24,X22)|~m2_yellow_6(X24,X22,X23)|(v2_struct_0(X22)|~l1_struct_0(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.20/0.42  cnf(c_0_25, negated_conjecture, (m2_yellow_6(esk7_1(X1),esk5_0,X1)|v2_struct_0(X1)|v1_compts_1(esk5_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (v1_compts_1(esk5_0)|l1_waybel_0(esk4_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (v1_compts_1(esk5_0)|v4_orders_2(esk4_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, (v1_compts_1(esk5_0)|v7_waybel_0(esk4_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.42  cnf(c_0_29, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  fof(c_0_30, plain, ![X20, X21]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20)|m1_subset_1(k10_yellow_6(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.20/0.42  cnf(c_0_31, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (v1_compts_1(esk5_0)|m2_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0,esk4_1(esk5_0))|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.20/0.42  cnf(c_0_33, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_19])).
% 0.20/0.42  cnf(c_0_34, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_35, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_36, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  fof(c_0_37, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|m1_subset_1(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.42  cnf(c_0_38, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (v1_compts_1(esk5_0)|l1_waybel_0(esk7_1(esk4_1(esk5_0)),esk5_0)|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), c_0_20]), c_0_27]), c_0_28]), c_0_26])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (v1_compts_1(esk5_0)|v4_orders_2(esk7_1(esk4_1(esk5_0)))|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_33])]), c_0_20]), c_0_27]), c_0_28]), c_0_26])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, (v1_compts_1(esk5_0)|v7_waybel_0(esk7_1(esk4_1(esk5_0)))|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_33])]), c_0_20]), c_0_27]), c_0_28]), c_0_26])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|~v2_struct_0(esk7_1(esk4_1(esk5_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_32]), c_0_33])]), c_0_20]), c_0_27]), c_0_28]), c_0_26])).
% 0.20/0.42  cnf(c_0_43, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|m1_subset_1(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_18]), c_0_19])]), c_0_20]), c_0_40]), c_0_41]), c_0_42])).
% 0.20/0.42  fof(c_0_45, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.42  fof(c_0_46, plain, ![X27, X28, X29]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27)|(~m1_subset_1(X29,u1_struct_0(X27))|(~r2_hidden(X29,k10_yellow_6(X27,X28))|r3_waybel_9(X27,X28,X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.20/0.42  fof(c_0_47, plain, ![X30, X31, X32, X33]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30)|(~m2_yellow_6(X32,X30,X31)|(~m1_subset_1(X33,u1_struct_0(X30))|(~r3_waybel_9(X30,X32,X33)|r3_waybel_9(X30,X31,X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).
% 0.20/0.42  cnf(c_0_48, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.42  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.42  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~r3_waybel_9(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|m1_subset_1(esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1),u1_struct_0(esk5_0))|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.42  cnf(c_0_53, plain, (r3_waybel_9(X1,X2,esk1_2(k10_yellow_6(X1,X2),X3))|v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(k10_yellow_6(X1,X2),X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(k10_yellow_6(X1,X2),X3),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, (v1_compts_1(esk5_0)|r3_waybel_9(esk5_0,X1,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))|v2_struct_0(esk4_1(esk5_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2)|~r3_waybel_9(esk5_0,X3,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))|~m2_yellow_6(X3,esk5_0,X1)|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.42  cnf(c_0_55, negated_conjecture, (v1_compts_1(esk5_0)|r3_waybel_9(esk5_0,esk7_1(esk4_1(esk5_0)),esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1))|v2_struct_0(esk4_1(esk5_0))|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_18]), c_0_19])]), c_0_20]), c_0_40]), c_0_41]), c_0_39]), c_0_42])).
% 0.20/0.42  fof(c_0_56, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.42  fof(c_0_57, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (v1_compts_1(esk5_0)|r3_waybel_9(esk5_0,X1,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))|v2_struct_0(esk4_1(esk5_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2)|~m2_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0,X1)|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.42  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.42  cnf(c_0_60, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.42  cnf(c_0_61, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk4_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (v1_compts_1(esk5_0)|r3_waybel_9(esk5_0,esk4_1(esk5_0),esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1))|v2_struct_0(esk4_1(esk5_0))|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_32]), c_0_27]), c_0_28]), c_0_26])).
% 0.20/0.42  fof(c_0_63, plain, ![X25, X26]:((~v3_yellow_6(X26,X25)|k10_yellow_6(X25,X26)!=k1_xboole_0|(v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(k10_yellow_6(X25,X26)=k1_xboole_0|v3_yellow_6(X26,X25)|(v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.20/0.42  cnf(c_0_64, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_18]), c_0_19])]), c_0_20]), c_0_52])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (v3_yellow_6(esk7_1(X1),esk5_0)|v2_struct_0(X1)|v1_compts_1(esk5_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  fof(c_0_67, plain, ![X34, X35, X36]:((m2_yellow_6(esk2_3(X34,X35,X36),X34,X35)|~r3_waybel_9(X34,X35,X36)|~m1_subset_1(X36,u1_struct_0(X34))|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(r2_hidden(X36,k10_yellow_6(X34,esk2_3(X34,X35,X36)))|~r3_waybel_9(X34,X35,X36)|~m1_subset_1(X36,u1_struct_0(X34))|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.20/0.42  cnf(c_0_68, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (v4_orders_2(esk6_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (v7_waybel_0(esk6_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_72, negated_conjecture, (~v2_struct_0(esk6_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_73, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0)))=k1_xboole_0|v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (v1_compts_1(esk5_0)|v3_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0)|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_26]), c_0_27]), c_0_28])).
% 0.20/0.42  cnf(c_0_76, plain, (m2_yellow_6(esk2_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.42  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0))|~v1_compts_1(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_18]), c_0_19])]), c_0_20]), c_0_70]), c_0_71]), c_0_72])).
% 0.20/0.42  cnf(c_0_78, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk4_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_79, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_18]), c_0_19])]), c_0_20]), c_0_40]), c_0_41]), c_0_39]), c_0_75]), c_0_42])).
% 0.20/0.42  cnf(c_0_80, plain, (r3_waybel_9(X1,X2,esk3_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_81, plain, (r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (m2_yellow_6(esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0)),esk5_0,X1)|v2_struct_0(X1)|~v1_compts_1(esk5_0)|~r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, (v1_compts_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.42  cnf(c_0_84, negated_conjecture, (r3_waybel_9(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))|~v1_compts_1(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_69]), c_0_18]), c_0_19])]), c_0_20]), c_0_70]), c_0_71]), c_0_72])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0))))|~v1_compts_1(esk5_0)|~r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_77]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.42  cnf(c_0_86, negated_conjecture, (m2_yellow_6(esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0)),esk5_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 0.20/0.42  cnf(c_0_87, negated_conjecture, (r3_waybel_9(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_83])])).
% 0.20/0.42  cnf(c_0_88, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_83])])).
% 0.20/0.42  cnf(c_0_89, negated_conjecture, (v7_waybel_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_83])])).
% 0.20/0.42  cnf(c_0_90, negated_conjecture, (v4_orders_2(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_83])])).
% 0.20/0.42  cnf(c_0_91, negated_conjecture, (~v2_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_83])])).
% 0.20/0.42  cnf(c_0_92, negated_conjecture, (~m2_yellow_6(X1,esk5_0,esk6_0)|~v3_yellow_6(X1,esk5_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  fof(c_0_93, plain, ![X17, X18]:(~r2_hidden(X17,X18)|~r1_tarski(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.42  cnf(c_0_94, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0))))|~r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_83])])).
% 0.20/0.42  cnf(c_0_95, negated_conjecture, (m2_yellow_6(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_89]), c_0_90])]), c_0_91])).
% 0.20/0.42  cnf(c_0_96, negated_conjecture, (~v3_yellow_6(X1,esk5_0)|~m2_yellow_6(X1,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_83])])).
% 0.20/0.42  cnf(c_0_97, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.20/0.42  cnf(c_0_98, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_87]), c_0_88]), c_0_89]), c_0_90])]), c_0_91])).
% 0.20/0.42  cnf(c_0_99, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.42  cnf(c_0_100, negated_conjecture, (l1_waybel_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_95]), c_0_88]), c_0_89]), c_0_90]), c_0_33])]), c_0_91]), c_0_20])).
% 0.20/0.42  cnf(c_0_101, negated_conjecture, (v7_waybel_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_95]), c_0_88]), c_0_89]), c_0_90]), c_0_33])]), c_0_91]), c_0_20])).
% 0.20/0.42  cnf(c_0_102, negated_conjecture, (v4_orders_2(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_95]), c_0_88]), c_0_89]), c_0_90]), c_0_33])]), c_0_91]), c_0_20])).
% 0.20/0.42  cnf(c_0_103, negated_conjecture, (~v3_yellow_6(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_96, c_0_95])).
% 0.20/0.42  cnf(c_0_104, negated_conjecture, (~v2_struct_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_95]), c_0_88]), c_0_89]), c_0_90]), c_0_33])]), c_0_91]), c_0_20])).
% 0.20/0.42  cnf(c_0_105, negated_conjecture, (~r1_tarski(k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))),esk3_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.42  cnf(c_0_106, negated_conjecture, (k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101]), c_0_102]), c_0_18]), c_0_19])]), c_0_103]), c_0_104]), c_0_20])).
% 0.20/0.42  cnf(c_0_107, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_60])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 108
% 0.20/0.42  # Proof object clause steps            : 79
% 0.20/0.42  # Proof object formula steps           : 29
% 0.20/0.42  # Proof object conjectures             : 56
% 0.20/0.42  # Proof object clause conjectures      : 53
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 34
% 0.20/0.42  # Proof object initial formulas used   : 14
% 0.20/0.42  # Proof object generating inferences   : 36
% 0.20/0.42  # Proof object simplifying inferences  : 164
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 14
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 38
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 38
% 0.20/0.42  # Processed clauses                    : 200
% 0.20/0.42  # ...of these trivial                  : 3
% 0.20/0.42  # ...subsumed                          : 12
% 0.20/0.42  # ...remaining for further processing  : 185
% 0.20/0.42  # Other redundant clauses eliminated   : 2
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 64
% 0.20/0.42  # Backward-rewritten                   : 23
% 0.20/0.42  # Generated clauses                    : 181
% 0.20/0.42  # ...of the previous two non-trivial   : 169
% 0.20/0.42  # Contextual simplify-reflections      : 166
% 0.20/0.42  # Paramodulations                      : 179
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 2
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 59
% 0.20/0.42  #    Positive orientable unit clauses  : 17
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 4
% 0.20/0.42  #    Non-unit-clauses                  : 38
% 0.20/0.42  # Current number of unprocessed clauses: 31
% 0.20/0.42  # ...number of literals in the above   : 218
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 124
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 8539
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 1309
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 242
% 0.20/0.42  # Unit Clause-clause subsumption calls : 93
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 7
% 0.20/0.42  # BW rewrite match successes           : 2
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 11823
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.076 s
% 0.20/0.42  # System time              : 0.007 s
% 0.20/0.42  # Total time               : 0.083 s
% 0.20/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
