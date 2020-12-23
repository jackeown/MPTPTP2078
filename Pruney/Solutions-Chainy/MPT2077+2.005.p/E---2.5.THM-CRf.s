%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:06 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  112 (141988 expanded)
%              Number of clauses        :   81 (46437 expanded)
%              Number of leaves         :   15 (35164 expanded)
%              Depth                    :   21
%              Number of atoms          :  617 (1703031 expanded)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    ! [X40,X41,X44] :
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
        | ~ l1_pre_topc(X40) )
      & ( ~ v2_struct_0(esk4_1(X40))
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v4_orders_2(esk4_1(X40))
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v7_waybel_0(esk4_1(X40))
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( l1_waybel_0(esk4_1(X40),X40)
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ m1_subset_1(X44,u1_struct_0(X40))
        | ~ r3_waybel_9(X40,esk4_1(X40),X44)
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).

fof(c_0_17,negated_conjecture,(
    ! [X47,X48] :
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
      & ( ~ m2_yellow_6(X47,esk5_0,esk6_0)
        | ~ v3_yellow_6(X47,esk5_0)
        | ~ v1_compts_1(esk5_0) )
      & ( m2_yellow_6(esk7_1(X48),esk5_0,X48)
        | v2_struct_0(X48)
        | ~ v4_orders_2(X48)
        | ~ v7_waybel_0(X48)
        | ~ l1_waybel_0(X48,esk5_0)
        | v1_compts_1(esk5_0) )
      & ( v3_yellow_6(esk7_1(X48),esk5_0)
        | v2_struct_0(X48)
        | ~ v4_orders_2(X48)
        | ~ v7_waybel_0(X48)
        | ~ l1_waybel_0(X48,esk5_0)
        | v1_compts_1(esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

cnf(c_0_18,plain,
    ( l1_waybel_0(esk4_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v4_orders_2(esk4_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v7_waybel_0(esk4_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_25,plain,(
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

cnf(c_0_26,negated_conjecture,
    ( m2_yellow_6(esk7_1(X1),esk5_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk5_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | l1_waybel_0(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v7_waybel_0(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
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
    ( v1_compts_1(esk5_0)
    | m2_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0,esk4_1(esk5_0))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
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
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
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
    ( v1_compts_1(esk5_0)
    | l1_waybel_0(esk7_1(esk4_1(esk5_0)),esk5_0)
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])]),c_0_21]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v4_orders_2(esk7_1(esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_34])]),c_0_21]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v7_waybel_0(esk7_1(esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_34])]),c_0_21]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | ~ v2_struct_0(esk7_1(esk4_1(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34])]),c_0_21]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
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

fof(c_0_48,plain,(
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

cnf(c_0_49,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | m1_subset_1(esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1),u1_struct_0(esk5_0))
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
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
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

fof(c_0_55,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_56,plain,(
    ! [X13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_57,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_58,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | r3_waybel_9(esk5_0,esk7_1(esk4_1(esk5_0)),esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1))
    | v2_struct_0(esk4_1(esk5_0))
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_19]),c_0_20])]),c_0_21]),c_0_41]),c_0_42]),c_0_40]),c_0_43])).

fof(c_0_59,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | r3_waybel_9(esk5_0,X1,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))
    | v2_struct_0(esk4_1(esk5_0))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2)
    | ~ m2_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0,X1)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk4_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | r3_waybel_9(esk5_0,esk4_1(esk5_0),esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1))
    | v2_struct_0(esk4_1(esk5_0))
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_33]),c_0_28]),c_0_29]),c_0_27])).

fof(c_0_67,plain,(
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

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_19]),c_0_20])]),c_0_21]),c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( v3_yellow_6(esk7_1(X1),esk5_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk5_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_71,plain,(
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

cnf(c_0_72,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,negated_conjecture,
    ( v4_orders_2(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_75,negated_conjecture,
    ( v7_waybel_0(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))) = k1_xboole_0
    | v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v3_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0)
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_80,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ v1_compts_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_19]),c_0_20])]),c_0_21]),c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_82,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk4_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_83,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_19]),c_0_20])]),c_0_21]),c_0_41]),c_0_42]),c_0_40]),c_0_79]),c_0_43])).

cnf(c_0_84,plain,
    ( r3_waybel_9(X1,X2,esk3_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_85,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_86,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0)),esk5_0,X1)
    | v2_struct_0(X1)
    | ~ v1_compts_1(esk5_0)
    | ~ r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_87,negated_conjecture,
    ( v1_compts_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( r3_waybel_9(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))
    | ~ v1_compts_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_73]),c_0_19]),c_0_20])]),c_0_21]),c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_89,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0))))
    | ~ v1_compts_1(esk5_0)
    | ~ r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_81]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_90,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0)),esk5_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_91,negated_conjecture,
    ( r3_waybel_9(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_87])])).

cnf(c_0_92,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_87])])).

cnf(c_0_93,negated_conjecture,
    ( v7_waybel_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_87])])).

cnf(c_0_94,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_87])])).

cnf(c_0_95,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_87])])).

cnf(c_0_96,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk5_0,esk6_0)
    | ~ v3_yellow_6(X1,esk5_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_97,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | ~ r1_tarski(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_98,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0))))
    | ~ r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_87])])).

cnf(c_0_99,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_93]),c_0_94])]),c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( ~ v3_yellow_6(X1,esk5_0)
    | ~ m2_yellow_6(X1,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_87])])).

cnf(c_0_101,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_91]),c_0_92]),c_0_93]),c_0_94])]),c_0_95])).

cnf(c_0_103,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_104,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_99]),c_0_92]),c_0_93]),c_0_94]),c_0_34])]),c_0_95]),c_0_21])).

cnf(c_0_105,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_99]),c_0_92]),c_0_93]),c_0_94]),c_0_34])]),c_0_95]),c_0_21])).

cnf(c_0_106,negated_conjecture,
    ( v4_orders_2(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_99]),c_0_92]),c_0_93]),c_0_94]),c_0_34])]),c_0_95]),c_0_21])).

cnf(c_0_107,negated_conjecture,
    ( ~ v3_yellow_6(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( ~ v2_struct_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_99]),c_0_92]),c_0_93]),c_0_94]),c_0_34])]),c_0_95]),c_0_21])).

cnf(c_0_109,negated_conjecture,
    ( ~ r1_tarski(k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))),esk3_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_106]),c_0_19]),c_0_20])]),c_0_107]),c_0_108]),c_0_21])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:52:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.40/0.58  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.40/0.58  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.40/0.58  #
% 0.40/0.58  # Preprocessing time       : 0.032 s
% 0.40/0.58  # Presaturation interreduction done
% 0.40/0.58  
% 0.40/0.58  # Proof found!
% 0.40/0.58  # SZS status Theorem
% 0.40/0.58  # SZS output start CNFRefutation
% 0.40/0.58  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 0.40/0.58  fof(t35_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_yellow19)).
% 0.40/0.58  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.40/0.58  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.40/0.58  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.40/0.58  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.40/0.58  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.40/0.58  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.40/0.58  fof(t31_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 0.40/0.58  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.40/0.58  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.40/0.58  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.40/0.58  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.40/0.58  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.40/0.58  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.40/0.58  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.40/0.58  fof(c_0_16, plain, ![X40, X41, X44]:(((m1_subset_1(esk3_2(X40,X41),u1_struct_0(X40))|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X40))|~v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(r3_waybel_9(X40,X41,esk3_2(X40,X41))|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X40))|~v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(((((~v2_struct_0(esk4_1(X40))|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(v4_orders_2(esk4_1(X40))|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(v7_waybel_0(esk4_1(X40))|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(l1_waybel_0(esk4_1(X40),X40)|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(~m1_subset_1(X44,u1_struct_0(X40))|~r3_waybel_9(X40,esk4_1(X40),X44)|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).
% 0.40/0.58  fof(c_0_17, negated_conjecture, ![X47, X48]:(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((((((~v2_struct_0(esk6_0)|~v1_compts_1(esk5_0))&(v4_orders_2(esk6_0)|~v1_compts_1(esk5_0)))&(v7_waybel_0(esk6_0)|~v1_compts_1(esk5_0)))&(l1_waybel_0(esk6_0,esk5_0)|~v1_compts_1(esk5_0)))&(~m2_yellow_6(X47,esk5_0,esk6_0)|~v3_yellow_6(X47,esk5_0)|~v1_compts_1(esk5_0)))&((m2_yellow_6(esk7_1(X48),esk5_0,X48)|(v2_struct_0(X48)|~v4_orders_2(X48)|~v7_waybel_0(X48)|~l1_waybel_0(X48,esk5_0))|v1_compts_1(esk5_0))&(v3_yellow_6(esk7_1(X48),esk5_0)|(v2_struct_0(X48)|~v4_orders_2(X48)|~v7_waybel_0(X48)|~l1_waybel_0(X48,esk5_0))|v1_compts_1(esk5_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.40/0.58  cnf(c_0_18, plain, (l1_waybel_0(esk4_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.58  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  cnf(c_0_22, plain, (v4_orders_2(esk4_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.58  cnf(c_0_23, plain, (v7_waybel_0(esk4_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.58  fof(c_0_24, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.40/0.58  fof(c_0_25, plain, ![X24, X25, X26]:((((~v2_struct_0(X26)|~m2_yellow_6(X26,X24,X25)|(v2_struct_0(X24)|~l1_struct_0(X24)|v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24)))&(v4_orders_2(X26)|~m2_yellow_6(X26,X24,X25)|(v2_struct_0(X24)|~l1_struct_0(X24)|v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24))))&(v7_waybel_0(X26)|~m2_yellow_6(X26,X24,X25)|(v2_struct_0(X24)|~l1_struct_0(X24)|v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24))))&(l1_waybel_0(X26,X24)|~m2_yellow_6(X26,X24,X25)|(v2_struct_0(X24)|~l1_struct_0(X24)|v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.40/0.58  cnf(c_0_26, negated_conjecture, (m2_yellow_6(esk7_1(X1),esk5_0,X1)|v2_struct_0(X1)|v1_compts_1(esk5_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  cnf(c_0_27, negated_conjecture, (v1_compts_1(esk5_0)|l1_waybel_0(esk4_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), c_0_21])).
% 0.40/0.58  cnf(c_0_28, negated_conjecture, (v1_compts_1(esk5_0)|v4_orders_2(esk4_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_20])]), c_0_21])).
% 0.40/0.58  cnf(c_0_29, negated_conjecture, (v1_compts_1(esk5_0)|v7_waybel_0(esk4_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_20])]), c_0_21])).
% 0.40/0.58  cnf(c_0_30, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.40/0.58  fof(c_0_31, plain, ![X22, X23]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22)|m1_subset_1(k10_yellow_6(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.40/0.58  cnf(c_0_32, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.40/0.58  cnf(c_0_33, negated_conjecture, (v1_compts_1(esk5_0)|m2_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0,esk4_1(esk5_0))|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.40/0.58  cnf(c_0_34, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.40/0.58  cnf(c_0_35, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.40/0.58  cnf(c_0_36, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.40/0.58  cnf(c_0_37, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.40/0.58  fof(c_0_38, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.40/0.58  cnf(c_0_39, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.40/0.58  cnf(c_0_40, negated_conjecture, (v1_compts_1(esk5_0)|l1_waybel_0(esk7_1(esk4_1(esk5_0)),esk5_0)|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])]), c_0_21]), c_0_28]), c_0_29]), c_0_27])).
% 0.40/0.58  cnf(c_0_41, negated_conjecture, (v1_compts_1(esk5_0)|v4_orders_2(esk7_1(esk4_1(esk5_0)))|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_33]), c_0_34])]), c_0_21]), c_0_28]), c_0_29]), c_0_27])).
% 0.40/0.58  cnf(c_0_42, negated_conjecture, (v1_compts_1(esk5_0)|v7_waybel_0(esk7_1(esk4_1(esk5_0)))|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_34])]), c_0_21]), c_0_28]), c_0_29]), c_0_27])).
% 0.40/0.58  cnf(c_0_43, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|~v2_struct_0(esk7_1(esk4_1(esk5_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_34])]), c_0_21]), c_0_28]), c_0_29]), c_0_27])).
% 0.40/0.58  cnf(c_0_44, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.40/0.58  cnf(c_0_45, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|m1_subset_1(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_19]), c_0_20])]), c_0_21]), c_0_41]), c_0_42]), c_0_43])).
% 0.40/0.58  fof(c_0_46, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.40/0.58  fof(c_0_47, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(v2_struct_0(X30)|~v4_orders_2(X30)|~v7_waybel_0(X30)|~l1_waybel_0(X30,X29)|(~m1_subset_1(X31,u1_struct_0(X29))|(~r2_hidden(X31,k10_yellow_6(X29,X30))|r3_waybel_9(X29,X30,X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.40/0.58  fof(c_0_48, plain, ![X32, X33, X34, X35]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32)|(~m2_yellow_6(X34,X32,X33)|(~m1_subset_1(X35,u1_struct_0(X32))|(~r3_waybel_9(X32,X34,X35)|r3_waybel_9(X32,X33,X35)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).
% 0.40/0.58  cnf(c_0_49, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.40/0.58  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.40/0.58  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.40/0.58  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~r3_waybel_9(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.40/0.58  cnf(c_0_53, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|m1_subset_1(esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1),u1_struct_0(esk5_0))|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.40/0.58  cnf(c_0_54, plain, (r3_waybel_9(X1,X2,esk1_2(k10_yellow_6(X1,X2),X3))|v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(k10_yellow_6(X1,X2),X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(k10_yellow_6(X1,X2),X3),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 0.40/0.58  fof(c_0_55, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.40/0.58  fof(c_0_56, plain, ![X13]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.40/0.58  cnf(c_0_57, negated_conjecture, (v1_compts_1(esk5_0)|r3_waybel_9(esk5_0,X1,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))|v2_struct_0(esk4_1(esk5_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2)|~r3_waybel_9(esk5_0,X3,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))|~m2_yellow_6(X3,esk5_0,X1)|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_19]), c_0_20])]), c_0_21])).
% 0.40/0.58  cnf(c_0_58, negated_conjecture, (v1_compts_1(esk5_0)|r3_waybel_9(esk5_0,esk7_1(esk4_1(esk5_0)),esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1))|v2_struct_0(esk4_1(esk5_0))|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_53]), c_0_19]), c_0_20])]), c_0_21]), c_0_41]), c_0_42]), c_0_40]), c_0_43])).
% 0.40/0.58  fof(c_0_59, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.40/0.58  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.40/0.58  cnf(c_0_61, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.40/0.58  cnf(c_0_62, negated_conjecture, (v1_compts_1(esk5_0)|r3_waybel_9(esk5_0,X1,esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2))|v2_struct_0(esk4_1(esk5_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X2)|~m2_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0,X1)|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.40/0.58  cnf(c_0_63, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.40/0.58  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.40/0.58  cnf(c_0_65, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk4_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.58  cnf(c_0_66, negated_conjecture, (v1_compts_1(esk5_0)|r3_waybel_9(esk5_0,esk4_1(esk5_0),esk1_2(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1))|v2_struct_0(esk4_1(esk5_0))|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_33]), c_0_28]), c_0_29]), c_0_27])).
% 0.40/0.58  fof(c_0_67, plain, ![X27, X28]:((~v3_yellow_6(X28,X27)|k10_yellow_6(X27,X28)!=k1_xboole_0|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(k10_yellow_6(X27,X28)=k1_xboole_0|v3_yellow_6(X28,X27)|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.40/0.58  cnf(c_0_68, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.40/0.58  cnf(c_0_69, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))|r1_tarski(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_19]), c_0_20])]), c_0_21]), c_0_53])).
% 0.40/0.58  cnf(c_0_70, negated_conjecture, (v3_yellow_6(esk7_1(X1),esk5_0)|v2_struct_0(X1)|v1_compts_1(esk5_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  fof(c_0_71, plain, ![X36, X37, X38]:((m2_yellow_6(esk2_3(X36,X37,X38),X36,X37)|~r3_waybel_9(X36,X37,X38)|~m1_subset_1(X38,u1_struct_0(X36))|(v2_struct_0(X37)|~v4_orders_2(X37)|~v7_waybel_0(X37)|~l1_waybel_0(X37,X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(r2_hidden(X38,k10_yellow_6(X36,esk2_3(X36,X37,X38)))|~r3_waybel_9(X36,X37,X38)|~m1_subset_1(X38,u1_struct_0(X36))|(v2_struct_0(X37)|~v4_orders_2(X37)|~v7_waybel_0(X37)|~l1_waybel_0(X37,X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.40/0.58  cnf(c_0_72, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.58  cnf(c_0_73, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  cnf(c_0_74, negated_conjecture, (v4_orders_2(esk6_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  cnf(c_0_75, negated_conjecture, (v7_waybel_0(esk6_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  cnf(c_0_76, negated_conjecture, (~v2_struct_0(esk6_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  cnf(c_0_77, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.40/0.58  cnf(c_0_78, negated_conjecture, (k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0)))=k1_xboole_0|v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.40/0.58  cnf(c_0_79, negated_conjecture, (v1_compts_1(esk5_0)|v3_yellow_6(esk7_1(esk4_1(esk5_0)),esk5_0)|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_27]), c_0_28]), c_0_29])).
% 0.40/0.58  cnf(c_0_80, plain, (m2_yellow_6(esk2_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.40/0.58  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0))|~v1_compts_1(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_19]), c_0_20])]), c_0_21]), c_0_74]), c_0_75]), c_0_76])).
% 0.40/0.58  cnf(c_0_82, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk4_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.58  cnf(c_0_83, negated_conjecture, (v1_compts_1(esk5_0)|v2_struct_0(esk4_1(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_19]), c_0_20])]), c_0_21]), c_0_41]), c_0_42]), c_0_40]), c_0_79]), c_0_43])).
% 0.40/0.58  cnf(c_0_84, plain, (r3_waybel_9(X1,X2,esk3_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.58  cnf(c_0_85, plain, (r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.40/0.58  cnf(c_0_86, negated_conjecture, (m2_yellow_6(esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0)),esk5_0,X1)|v2_struct_0(X1)|~v1_compts_1(esk5_0)|~r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_19]), c_0_20])]), c_0_21])).
% 0.40/0.58  cnf(c_0_87, negated_conjecture, (v1_compts_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_19]), c_0_20])]), c_0_21])).
% 0.40/0.58  cnf(c_0_88, negated_conjecture, (r3_waybel_9(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))|~v1_compts_1(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_73]), c_0_19]), c_0_20])]), c_0_21]), c_0_74]), c_0_75]), c_0_76])).
% 0.40/0.58  cnf(c_0_89, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0))))|~v1_compts_1(esk5_0)|~r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_81]), c_0_19]), c_0_20])]), c_0_21])).
% 0.40/0.58  cnf(c_0_90, negated_conjecture, (m2_yellow_6(esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0)),esk5_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.40/0.58  cnf(c_0_91, negated_conjecture, (r3_waybel_9(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_87])])).
% 0.40/0.58  cnf(c_0_92, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_87])])).
% 0.40/0.58  cnf(c_0_93, negated_conjecture, (v7_waybel_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_87])])).
% 0.40/0.58  cnf(c_0_94, negated_conjecture, (v4_orders_2(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_87])])).
% 0.40/0.58  cnf(c_0_95, negated_conjecture, (~v2_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_87])])).
% 0.40/0.58  cnf(c_0_96, negated_conjecture, (~m2_yellow_6(X1,esk5_0,esk6_0)|~v3_yellow_6(X1,esk5_0)|~v1_compts_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  fof(c_0_97, plain, ![X19, X20]:(~r2_hidden(X19,X20)|~r1_tarski(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.40/0.58  cnf(c_0_98, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,X1,esk3_2(esk5_0,esk6_0))))|~r3_waybel_9(esk5_0,X1,esk3_2(esk5_0,esk6_0))|~l1_waybel_0(X1,esk5_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_87])])).
% 0.40/0.58  cnf(c_0_99, negated_conjecture, (m2_yellow_6(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_93]), c_0_94])]), c_0_95])).
% 0.40/0.58  cnf(c_0_100, negated_conjecture, (~v3_yellow_6(X1,esk5_0)|~m2_yellow_6(X1,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_87])])).
% 0.40/0.58  cnf(c_0_101, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.40/0.58  cnf(c_0_102, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_91]), c_0_92]), c_0_93]), c_0_94])]), c_0_95])).
% 0.40/0.58  cnf(c_0_103, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.40/0.58  cnf(c_0_104, negated_conjecture, (l1_waybel_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_99]), c_0_92]), c_0_93]), c_0_94]), c_0_34])]), c_0_95]), c_0_21])).
% 0.40/0.58  cnf(c_0_105, negated_conjecture, (v7_waybel_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_99]), c_0_92]), c_0_93]), c_0_94]), c_0_34])]), c_0_95]), c_0_21])).
% 0.40/0.58  cnf(c_0_106, negated_conjecture, (v4_orders_2(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_99]), c_0_92]), c_0_93]), c_0_94]), c_0_34])]), c_0_95]), c_0_21])).
% 0.40/0.58  cnf(c_0_107, negated_conjecture, (~v3_yellow_6(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_100, c_0_99])).
% 0.40/0.58  cnf(c_0_108, negated_conjecture, (~v2_struct_0(esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_99]), c_0_92]), c_0_93]), c_0_94]), c_0_34])]), c_0_95]), c_0_21])).
% 0.40/0.58  cnf(c_0_109, negated_conjecture, (~r1_tarski(k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0))),esk3_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.40/0.58  cnf(c_0_110, negated_conjecture, (k10_yellow_6(esk5_0,esk2_3(esk5_0,esk6_0,esk3_2(esk5_0,esk6_0)))=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105]), c_0_106]), c_0_19]), c_0_20])]), c_0_107]), c_0_108]), c_0_21])).
% 0.40/0.58  cnf(c_0_111, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_64])]), ['proof']).
% 0.40/0.58  # SZS output end CNFRefutation
% 0.40/0.58  # Proof object total steps             : 112
% 0.40/0.58  # Proof object clause steps            : 81
% 0.40/0.58  # Proof object formula steps           : 31
% 0.40/0.58  # Proof object conjectures             : 56
% 0.40/0.58  # Proof object clause conjectures      : 53
% 0.40/0.58  # Proof object formula conjectures     : 3
% 0.40/0.58  # Proof object initial clauses used    : 35
% 0.40/0.58  # Proof object initial formulas used   : 15
% 0.40/0.58  # Proof object generating inferences   : 37
% 0.40/0.58  # Proof object simplifying inferences  : 164
% 0.40/0.58  # Training examples: 0 positive, 0 negative
% 0.40/0.58  # Parsed axioms                        : 15
% 0.40/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.58  # Initial clauses                      : 40
% 0.40/0.58  # Removed in clause preprocessing      : 0
% 0.40/0.58  # Initial clauses in saturation        : 40
% 0.40/0.58  # Processed clauses                    : 1795
% 0.40/0.58  # ...of these trivial                  : 3
% 0.40/0.58  # ...subsumed                          : 1021
% 0.40/0.58  # ...remaining for further processing  : 771
% 0.40/0.58  # Other redundant clauses eliminated   : 2
% 0.40/0.58  # Clauses deleted for lack of memory   : 0
% 0.40/0.58  # Backward-subsumed                    : 506
% 0.40/0.58  # Backward-rewritten                   : 27
% 0.40/0.58  # Generated clauses                    : 3744
% 0.40/0.58  # ...of the previous two non-trivial   : 3442
% 0.40/0.58  # Contextual simplify-reflections      : 643
% 0.40/0.58  # Paramodulations                      : 3736
% 0.40/0.58  # Factorizations                       : 6
% 0.40/0.58  # Equation resolutions                 : 2
% 0.40/0.58  # Propositional unsat checks           : 0
% 0.40/0.58  #    Propositional check models        : 0
% 0.40/0.58  #    Propositional check unsatisfiable : 0
% 0.40/0.58  #    Propositional clauses             : 0
% 0.40/0.58  #    Propositional clauses after purity: 0
% 0.40/0.58  #    Propositional unsat core size     : 0
% 0.40/0.58  #    Propositional preprocessing time  : 0.000
% 0.40/0.58  #    Propositional encoding time       : 0.000
% 0.40/0.58  #    Propositional solver time         : 0.000
% 0.40/0.58  #    Success case prop preproc time    : 0.000
% 0.40/0.58  #    Success case prop encoding time   : 0.000
% 0.40/0.58  #    Success case prop solver time     : 0.000
% 0.40/0.58  # Current number of processed clauses  : 197
% 0.40/0.58  #    Positive orientable unit clauses  : 19
% 0.40/0.58  #    Positive unorientable unit clauses: 0
% 0.40/0.58  #    Negative unit clauses             : 4
% 0.40/0.58  #    Non-unit-clauses                  : 174
% 0.40/0.58  # Current number of unprocessed clauses: 1719
% 0.40/0.58  # ...number of literals in the above   : 10192
% 0.40/0.58  # Current number of archived formulas  : 0
% 0.40/0.58  # Current number of archived clauses   : 572
% 0.40/0.58  # Clause-clause subsumption calls (NU) : 246542
% 0.40/0.58  # Rec. Clause-clause subsumption calls : 22390
% 0.40/0.58  # Non-unit clause-clause subsumptions  : 2170
% 0.40/0.58  # Unit Clause-clause subsumption calls : 359
% 0.40/0.58  # Rewrite failures with RHS unbound    : 0
% 0.40/0.58  # BW rewrite match attempts            : 4
% 0.40/0.58  # BW rewrite match successes           : 2
% 0.40/0.58  # Condensation attempts                : 0
% 0.40/0.58  # Condensation successes               : 0
% 0.40/0.58  # Termbank termtop insertions          : 122000
% 0.40/0.58  
% 0.40/0.58  # -------------------------------------------------
% 0.40/0.58  # User time                : 0.232 s
% 0.40/0.58  # System time              : 0.010 s
% 0.40/0.58  # Total time               : 0.243 s
% 0.40/0.58  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
