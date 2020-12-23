%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:06 EST 2020

% Result     : Theorem 12.47s
% Output     : CNFRefutation 12.47s
% Verified   : 
% Statistics : Number of formulae       :  908 (568038946459421561648852431029758390365325361152 expanded)
%              Number of clauses        :  875 (195425413586127998724941379729233008999427735552 expanded)
%              Number of leaves         :   16 (134604307556277008011686979149142605514837852160 expanded)
%              Depth                    :  451
%              Number of atoms          : 4739 (6788271698234595971450545218539019297445552062464 expanded)
%              Number of equality atoms :   62 (3581914655486699616784982876205049466096451584 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   51 (   5 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_yellow19)).

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

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l37_yellow19)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_18,negated_conjecture,(
    ! [X47,X48] :
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
      & ( ~ m2_yellow_6(X47,esk6_0,esk7_0)
        | ~ v3_yellow_6(X47,esk6_0)
        | ~ v1_compts_1(esk6_0) )
      & ( m2_yellow_6(esk8_1(X48),esk6_0,X48)
        | v2_struct_0(X48)
        | ~ v4_orders_2(X48)
        | ~ v7_waybel_0(X48)
        | ~ l1_waybel_0(X48,esk6_0)
        | v1_compts_1(esk6_0) )
      & ( v3_yellow_6(esk8_1(X48),esk6_0)
        | v2_struct_0(X48)
        | ~ v4_orders_2(X48)
        | ~ v7_waybel_0(X48)
        | ~ l1_waybel_0(X48,esk6_0)
        | v1_compts_1(esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

fof(c_0_19,plain,(
    ! [X40,X41,X44] :
      ( ( m1_subset_1(esk4_2(X40,X41),u1_struct_0(X40))
        | ~ r2_hidden(X41,k6_yellow_6(X40))
        | v2_struct_0(X41)
        | ~ v4_orders_2(X41)
        | ~ v7_waybel_0(X41)
        | ~ l1_waybel_0(X41,X40)
        | ~ v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r3_waybel_9(X40,X41,esk4_2(X40,X41))
        | ~ r2_hidden(X41,k6_yellow_6(X40))
        | v2_struct_0(X41)
        | ~ v4_orders_2(X41)
        | ~ v7_waybel_0(X41)
        | ~ l1_waybel_0(X41,X40)
        | ~ v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ v2_struct_0(esk5_1(X40))
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v4_orders_2(esk5_1(X40))
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v7_waybel_0(esk5_1(X40))
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( l1_waybel_0(esk5_1(X40),X40)
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r2_hidden(esk5_1(X40),k6_yellow_6(X40))
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ m1_subset_1(X44,u1_struct_0(X40))
        | ~ r3_waybel_9(X40,esk5_1(X40),X44)
        | v1_compts_1(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_yellow19])])])])])])).

fof(c_0_20,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v2_struct_0(X23)
        | ~ m2_yellow_6(X23,X21,X22)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21) )
      & ( v4_orders_2(X23)
        | ~ m2_yellow_6(X23,X21,X22)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21) )
      & ( v7_waybel_0(X23)
        | ~ m2_yellow_6(X23,X21,X22)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21) )
      & ( l1_waybel_0(X23,X21)
        | ~ m2_yellow_6(X23,X21,X22)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_21,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v4_orders_2(esk5_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v7_waybel_0(esk5_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( l1_waybel_0(esk5_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_34,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk5_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_37,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | v2_struct_0(X20)
      | ~ v4_orders_2(X20)
      | ~ v7_waybel_0(X20)
      | ~ l1_waybel_0(X20,X19)
      | m1_subset_1(k10_yellow_6(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_38,negated_conjecture,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | ~ m2_yellow_6(X1,esk6_0,X2)
    | ~ l1_waybel_0(X2,esk6_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v4_orders_2(esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( m2_yellow_6(esk8_1(X1),esk6_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk6_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | ~ v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | ~ m2_yellow_6(X1,esk6_0,X2)
    | ~ l1_waybel_0(X2,esk6_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(X2)
    | ~ m2_yellow_6(X1,esk6_0,X2)
    | ~ l1_waybel_0(X2,esk6_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_25])).

fof(c_0_46,plain,(
    ! [X9,X10,X11] :
      ( ( m1_subset_1(esk1_3(X9,X10,X11),X9)
        | r1_tarski(X10,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X10)
        | r1_tarski(X10,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) )
      & ( ~ r2_hidden(esk1_3(X9,X10,X11),X11)
        | r1_tarski(X10,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_47,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v4_orders_2(X1)
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | v4_orders_2(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_40]),c_0_41]),c_0_43]),c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( v7_waybel_0(X1)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_53,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k10_yellow_6(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_50])).

fof(c_0_59,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk1_3(X1,X2,k1_xboole_0),X1)
    | r1_tarski(X2,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])).

fof(c_0_62,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_63,negated_conjecture,
    ( v3_yellow_6(esk8_1(X1),esk6_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk6_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_64,plain,(
    ! [X29,X30,X31,X32] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | v2_struct_0(X30)
      | ~ v4_orders_2(X30)
      | ~ v7_waybel_0(X30)
      | ~ l1_waybel_0(X30,X29)
      | ~ m2_yellow_6(X31,X29,X30)
      | ~ m1_subset_1(X32,u1_struct_0(X29))
      | ~ r3_waybel_9(X29,X31,X32)
      | r3_waybel_9(X29,X30,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

fof(c_0_65,plain,(
    ! [X24,X25] :
      ( ( ~ v3_yellow_6(X25,X24)
        | k10_yellow_6(X24,X25) != k1_xboole_0
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( k10_yellow_6(X24,X25) = k1_xboole_0
        | v3_yellow_6(X25,X24)
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

cnf(c_0_66,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk7_0)
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_39]),c_0_40]),c_0_43]),c_0_30])).

cnf(c_0_70,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk5_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_74,negated_conjecture,
    ( v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_41])).

fof(c_0_75,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ v4_orders_2(X27)
      | ~ v7_waybel_0(X27)
      | ~ l1_waybel_0(X27,X26)
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | ~ r2_hidden(X28,k10_yellow_6(X26,X27))
      | r3_waybel_9(X26,X27,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

fof(c_0_76,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | m1_subset_1(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_77,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk6_0,X3,X2)
    | ~ m2_yellow_6(X3,esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_78,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_79,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_24]),c_0_22])]),c_0_25]),c_0_56]),c_0_57]),c_0_58]),c_0_74])).

cnf(c_0_80,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_83,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_84,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_43]),c_0_30])).

cnf(c_0_85,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(X2,k10_yellow_6(esk6_0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_86,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_61])).

cnf(c_0_87,plain,
    ( r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2)
    | r1_tarski(X2,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_54])).

cnf(c_0_88,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_79]),c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_56]),c_0_86]),c_0_57]),c_0_58])).

cnf(c_0_90,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_61])).

cnf(c_0_91,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_50])).

fof(c_0_92,plain,(
    ! [X33,X34,X35] :
      ( ( m2_yellow_6(esk2_3(X33,X34,X35),X33,X34)
        | ~ r3_waybel_9(X33,X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r2_hidden(X35,k10_yellow_6(X33,esk2_3(X33,X34,X35)))
        | ~ r3_waybel_9(X33,X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_93,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

fof(c_0_94,plain,(
    ! [X37,X38] :
      ( ( m1_subset_1(esk3_2(X37,X38),u1_struct_0(X37))
        | v2_struct_0(X38)
        | ~ v4_orders_2(X38)
        | ~ v7_waybel_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | ~ v1_compts_1(X37)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r3_waybel_9(X37,X38,esk3_2(X37,X38))
        | v2_struct_0(X38)
        | ~ v4_orders_2(X38)
        | ~ v7_waybel_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | ~ v1_compts_1(X37)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).

cnf(c_0_95,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_93]),c_0_68])])).

cnf(c_0_97,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_98,plain,
    ( r3_waybel_9(X1,X2,esk3_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,X1,X2),esk6_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk6_0,X1,X2)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_100,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_96]),c_0_24]),c_0_22])]),c_0_25]),c_0_56]),c_0_57]),c_0_58]),c_0_74])).

cnf(c_0_101,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_102,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_103,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_104,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ v1_compts_1(esk6_0)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_105,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v2_struct_0(X1)
    | ~ v1_compts_1(esk6_0)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_106,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_107,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v4_orders_2(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_31])).

cnf(c_0_109,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_31])).

cnf(c_0_110,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_31])).

cnf(c_0_111,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_31])).

cnf(c_0_112,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_31])).

cnf(c_0_113,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k10_yellow_6(esk6_0,esk2_3(esk6_0,X1,X2)))
    | ~ r3_waybel_9(esk6_0,X1,X2)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_114,negated_conjecture,
    ( v4_orders_2(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_100])).

cnf(c_0_115,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_100]),c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_117,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_100]),c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_118,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_100])).

cnf(c_0_119,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_100])).

cnf(c_0_120,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_100])).

cnf(c_0_121,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_122,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v4_orders_2(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_123,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])).

cnf(c_0_124,negated_conjecture,
    ( v7_waybel_0(X1)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_125,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_108]),c_0_109]),c_0_110])).

fof(c_0_126,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | ~ r1_tarski(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_127,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_128,negated_conjecture,
    ( k10_yellow_6(esk6_0,X1) = k1_xboole_0
    | v3_yellow_6(X1,esk6_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_22]),c_0_24])]),c_0_25])).

cnf(c_0_129,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_130,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_123])).

cnf(c_0_131,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_123])).

cnf(c_0_132,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_133,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ v1_compts_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_134,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_116]),c_0_117])).

cnf(c_0_135,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130]),c_0_131])).

cnf(c_0_136,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_68])).

cnf(c_0_137,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_31])).

cnf(c_0_138,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_123])).

cnf(c_0_140,negated_conjecture,
    ( v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_139])).

cnf(c_0_141,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_32])).

cnf(c_0_142,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_33])).

cnf(c_0_143,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_142])).

cnf(c_0_144,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_139]),c_0_32]),c_0_33]),c_0_43])).

cnf(c_0_145,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_43]),c_0_101])).

cnf(c_0_146,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_145])).

cnf(c_0_147,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v7_waybel_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_32])).

cnf(c_0_148,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_32])).

cnf(c_0_149,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_32])).

cnf(c_0_150,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_32])).

cnf(c_0_151,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_145])).

cnf(c_0_152,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_148])).

cnf(c_0_153,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_100]),c_0_141]),c_0_147]),c_0_148])).

cnf(c_0_154,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_100]),c_0_141]),c_0_147]),c_0_148])).

cnf(c_0_155,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_147]),c_0_148])).

cnf(c_0_156,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154])).

cnf(c_0_157,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_158,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_157])).

cnf(c_0_159,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_33])).

cnf(c_0_160,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_161,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_144]),c_0_43]),c_0_102])).

cnf(c_0_162,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_33])).

cnf(c_0_163,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_33])).

cnf(c_0_164,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_33])).

cnf(c_0_165,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_161])).

cnf(c_0_166,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_100]),c_0_142]),c_0_159]),c_0_163])).

cnf(c_0_167,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_100]),c_0_142]),c_0_159]),c_0_163])).

cnf(c_0_168,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_151,c_0_161])).

cnf(c_0_169,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_170,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_169]),c_0_163])).

cnf(c_0_171,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_170])).

cnf(c_0_172,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_144]),c_0_43])).

cnf(c_0_173,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_172])).

cnf(c_0_174,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_172])).

cnf(c_0_175,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_172])).

cnf(c_0_176,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_100]),c_0_145]),c_0_161]),c_0_174])).

cnf(c_0_177,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_100]),c_0_145]),c_0_161]),c_0_174])).

cnf(c_0_178,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_176]),c_0_177]),c_0_174])).

cnf(c_0_179,negated_conjecture,
    ( v7_waybel_0(X1)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_145])).

cnf(c_0_180,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_145])).

cnf(c_0_181,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_145])).

cnf(c_0_182,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_178]),c_0_174])).

cnf(c_0_183,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v7_waybel_0(X1)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_147]),c_0_148])).

cnf(c_0_184,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_147]),c_0_148])).

cnf(c_0_185,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_147]),c_0_148])).

cnf(c_0_186,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | ~ v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_128,c_0_182])).

cnf(c_0_187,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_183,c_0_156])).

cnf(c_0_188,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_184,c_0_156])).

cnf(c_0_189,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_153]),c_0_154])).

cnf(c_0_190,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_187]),c_0_188])).

cnf(c_0_191,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_32])).

cnf(c_0_192,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_190]),c_0_136])).

cnf(c_0_193,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_192]),c_0_156])).

cnf(c_0_194,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_193])).

cnf(c_0_195,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_194,c_0_159])).

cnf(c_0_196,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_144]),c_0_43]),c_0_102])).

cnf(c_0_197,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_196])).

cnf(c_0_198,negated_conjecture,
    ( v7_waybel_0(X1)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_179,c_0_196])).

cnf(c_0_199,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_200,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_199]),c_0_163])).

cnf(c_0_201,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_194,c_0_200])).

cnf(c_0_202,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_144]),c_0_43])).

cnf(c_0_203,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_202])).

cnf(c_0_204,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_202])).

cnf(c_0_205,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_202])).

cnf(c_0_206,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_100]),c_0_145]),c_0_196]),c_0_204])).

cnf(c_0_207,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_100]),c_0_145]),c_0_196]),c_0_204])).

cnf(c_0_208,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_206]),c_0_207]),c_0_204])).

cnf(c_0_209,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_208]),c_0_204])).

cnf(c_0_210,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_180,c_0_196])).

cnf(c_0_211,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_181,c_0_196])).

cnf(c_0_212,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_186,c_0_209])).

cnf(c_0_213,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_210,c_0_199]),c_0_163])).

cnf(c_0_214,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_215,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_212,c_0_213])).

cnf(c_0_216,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_33])).

cnf(c_0_217,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_214,c_0_215]),c_0_136])).

cnf(c_0_218,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_217]),c_0_199])).

cnf(c_0_219,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_194,c_0_218])).

cnf(c_0_220,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_219,c_0_144]),c_0_43])).

cnf(c_0_221,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_220])).

cnf(c_0_222,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_220])).

cnf(c_0_223,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_220])).

cnf(c_0_224,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_221,c_0_100]),c_0_145]),c_0_196]),c_0_222])).

cnf(c_0_225,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_223,c_0_100]),c_0_145]),c_0_196]),c_0_222])).

cnf(c_0_226,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_224]),c_0_225]),c_0_222])).

cnf(c_0_227,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_210,c_0_226]),c_0_222])).

cnf(c_0_228,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_224]),c_0_225]),c_0_222])).

cnf(c_0_229,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_212,c_0_227])).

cnf(c_0_230,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_220])).

cnf(c_0_231,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_228,c_0_229]),c_0_136])).

cnf(c_0_232,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_139])).

cnf(c_0_233,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_139])).

cnf(c_0_234,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_230,c_0_231]),c_0_226])).

cnf(c_0_235,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_232,c_0_141]),c_0_142])).

cnf(c_0_236,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_233,c_0_141]),c_0_142])).

cnf(c_0_237,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ v7_waybel_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_234])).

cnf(c_0_238,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_235,c_0_144]),c_0_43]),c_0_101])).

cnf(c_0_239,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_236,c_0_144]),c_0_43]),c_0_101])).

cnf(c_0_240,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_237,c_0_238]),c_0_239])).

cnf(c_0_241,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_240])).

cnf(c_0_242,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_241]),c_0_68])])).

cnf(c_0_243,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_242]),c_0_24]),c_0_22])]),c_0_25]),c_0_145]),c_0_238]),c_0_239])).

cnf(c_0_244,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_139]),c_0_32]),c_0_33]),c_0_43])).

cnf(c_0_245,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_139])).

cnf(c_0_246,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_244]),c_0_43]),c_0_101])).

cnf(c_0_247,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_245,c_0_141]),c_0_142])).

cnf(c_0_248,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_246]),c_0_101])).

cnf(c_0_249,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_234])).

cnf(c_0_250,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_240])).

cnf(c_0_251,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_246]),c_0_248])).

cnf(c_0_252,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_249,c_0_238]),c_0_250]),c_0_239])).

cnf(c_0_253,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_240])).

cnf(c_0_254,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_251,c_0_144]),c_0_43]),c_0_101])).

cnf(c_0_255,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_252,c_0_253]),c_0_254])).

cnf(c_0_256,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_255]),c_0_68])])).

cnf(c_0_257,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_256]),c_0_24]),c_0_22])]),c_0_25]),c_0_145]),c_0_238]),c_0_239])).

cnf(c_0_258,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_257,c_0_244]),c_0_43]),c_0_101])).

cnf(c_0_259,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_258])).

cnf(c_0_260,negated_conjecture,
    ( v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_258])).

cnf(c_0_261,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_259,c_0_147]),c_0_148])).

cnf(c_0_262,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_260,c_0_147]),c_0_148])).

cnf(c_0_263,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_261,c_0_153]),c_0_154])).

cnf(c_0_264,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_262,c_0_263])).

cnf(c_0_265,negated_conjecture,
    ( v7_waybel_0(X1)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_232,c_0_264])).

cnf(c_0_266,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v7_waybel_0(X1)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_265,c_0_159])).

cnf(c_0_267,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_266,c_0_144]),c_0_43]),c_0_102])).

cnf(c_0_268,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_259,c_0_267])).

cnf(c_0_269,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_260,c_0_267])).

cnf(c_0_270,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_268,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_271,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_269,c_0_270]),c_0_163])).

cnf(c_0_272,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v7_waybel_0(X1)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_265,c_0_271])).

cnf(c_0_273,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_272,c_0_144]),c_0_43])).

cnf(c_0_274,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_273])).

cnf(c_0_275,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_273])).

cnf(c_0_276,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_273])).

cnf(c_0_277,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_274,c_0_100]),c_0_258]),c_0_267]),c_0_275])).

cnf(c_0_278,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_276,c_0_100]),c_0_258]),c_0_267]),c_0_275])).

cnf(c_0_279,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_268,c_0_277]),c_0_278]),c_0_275])).

cnf(c_0_280,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_233,c_0_264])).

cnf(c_0_281,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_269,c_0_279]),c_0_275])).

cnf(c_0_282,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | l1_waybel_0(X1,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_280,c_0_159])).

cnf(c_0_283,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_237,c_0_281])).

cnf(c_0_284,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_282,c_0_144]),c_0_43]),c_0_102])).

cnf(c_0_285,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_283,c_0_284])).

cnf(c_0_286,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_285])).

cnf(c_0_287,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_286]),c_0_68])])).

cnf(c_0_288,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_287]),c_0_24]),c_0_22])]),c_0_25]),c_0_196]),c_0_267]),c_0_284])).

cnf(c_0_289,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_245,c_0_264])).

cnf(c_0_290,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_288,c_0_244]),c_0_43]),c_0_102])).

cnf(c_0_291,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_289,c_0_159])).

cnf(c_0_292,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_290]),c_0_102])).

cnf(c_0_293,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_249,c_0_281])).

cnf(c_0_294,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_291,c_0_290]),c_0_292])).

cnf(c_0_295,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_293,c_0_284])).

cnf(c_0_296,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_294,c_0_144]),c_0_43]),c_0_102])).

cnf(c_0_297,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_295,c_0_290]),c_0_296])).

cnf(c_0_298,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_285])).

cnf(c_0_299,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_297,c_0_298])).

cnf(c_0_300,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_299]),c_0_68])])).

cnf(c_0_301,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_300]),c_0_24]),c_0_22])]),c_0_25]),c_0_196]),c_0_267]),c_0_284])).

cnf(c_0_302,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_301,c_0_244]),c_0_43]),c_0_102])).

cnf(c_0_303,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_259,c_0_302])).

cnf(c_0_304,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_260,c_0_302])).

cnf(c_0_305,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_303,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_306,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_304,c_0_305]),c_0_163])).

cnf(c_0_307,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_280,c_0_306])).

cnf(c_0_308,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_307,c_0_144]),c_0_43])).

cnf(c_0_309,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_308])).

cnf(c_0_310,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_308])).

cnf(c_0_311,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_308])).

cnf(c_0_312,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_309,c_0_100]),c_0_258]),c_0_302]),c_0_310])).

cnf(c_0_313,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_311,c_0_100]),c_0_258]),c_0_302]),c_0_310])).

cnf(c_0_314,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_303,c_0_312]),c_0_313]),c_0_310])).

cnf(c_0_315,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_304,c_0_314]),c_0_310])).

cnf(c_0_316,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_283,c_0_315])).

cnf(c_0_317,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_316])).

cnf(c_0_318,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_317]),c_0_68])])).

cnf(c_0_319,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_318]),c_0_24]),c_0_22])]),c_0_25]),c_0_234]),c_0_281]),c_0_315])).

cnf(c_0_320,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_319,c_0_244]),c_0_43])).

cnf(c_0_321,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_320])).

cnf(c_0_322,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_320])).

cnf(c_0_323,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_289,c_0_306])).

cnf(c_0_324,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_321,c_0_100]),c_0_258]),c_0_302]),c_0_322])).

cnf(c_0_325,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_316])).

cnf(c_0_326,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_323,c_0_324])).

cnf(c_0_327,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_324]),c_0_43])).

cnf(c_0_328,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_293,c_0_315]),c_0_325])).

cnf(c_0_329,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_316])).

cnf(c_0_330,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_326,c_0_144]),c_0_43]),c_0_327])).

cnf(c_0_331,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_328,c_0_329])).

cnf(c_0_332,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_330,c_0_331]),c_0_43])).

cnf(c_0_333,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_332]),c_0_68])])).

cnf(c_0_334,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_333]),c_0_24]),c_0_22])]),c_0_25]),c_0_220]),c_0_273]),c_0_308]),c_0_244])).

cnf(c_0_335,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_334])).

cnf(c_0_336,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_334])).

cnf(c_0_337,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_335,c_0_100]),c_0_258]),c_0_302]),c_0_336])).

cnf(c_0_338,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_320])).

cnf(c_0_339,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_303,c_0_337])).

cnf(c_0_340,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_338,c_0_100]),c_0_258]),c_0_302]),c_0_322])).

cnf(c_0_341,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_339,c_0_340]),c_0_322])).

cnf(c_0_342,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_304,c_0_341]),c_0_322])).

cnf(c_0_343,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_323,c_0_342])).

cnf(c_0_344,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_342]),c_0_43])).

cnf(c_0_345,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_343,c_0_144]),c_0_43]),c_0_344])).

cnf(c_0_346,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_345,c_0_331]),c_0_43])).

cnf(c_0_347,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_346]),c_0_68])])).

cnf(c_0_348,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_347]),c_0_24]),c_0_22])]),c_0_25]),c_0_220]),c_0_273]),c_0_308]),c_0_244])).

cnf(c_0_349,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_348])).

cnf(c_0_350,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_348])).

cnf(c_0_351,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_349,c_0_100]),c_0_258]),c_0_302]),c_0_350])).

cnf(c_0_352,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_339,c_0_351]),c_0_350])).

cnf(c_0_353,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_258])).

cnf(c_0_354,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_258])).

cnf(c_0_355,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_258])).

cnf(c_0_356,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_304,c_0_352]),c_0_350])).

cnf(c_0_357,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_353,c_0_147]),c_0_148])).

cnf(c_0_358,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_354,c_0_147]),c_0_148])).

cnf(c_0_359,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_355,c_0_147]),c_0_148])).

cnf(c_0_360,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | ~ v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_128,c_0_356])).

cnf(c_0_361,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_357,c_0_263])).

cnf(c_0_362,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_358,c_0_263])).

cnf(c_0_363,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_359,c_0_153]),c_0_154])).

cnf(c_0_364,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_360,c_0_361]),c_0_362])).

cnf(c_0_365,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_363,c_0_364]),c_0_136])).

cnf(c_0_366,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_365]),c_0_263])).

cnf(c_0_367,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_232,c_0_366])).

cnf(c_0_368,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_367,c_0_159])).

cnf(c_0_369,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_368,c_0_144]),c_0_43]),c_0_102])).

cnf(c_0_370,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_259,c_0_369])).

cnf(c_0_371,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_353,c_0_369])).

cnf(c_0_372,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_370,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_373,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_371,c_0_372]),c_0_163])).

cnf(c_0_374,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_367,c_0_373])).

cnf(c_0_375,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_374,c_0_144]),c_0_43])).

cnf(c_0_376,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_375])).

cnf(c_0_377,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_375])).

cnf(c_0_378,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_375])).

cnf(c_0_379,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_376,c_0_100]),c_0_258]),c_0_369]),c_0_377])).

cnf(c_0_380,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_378,c_0_100]),c_0_258]),c_0_369]),c_0_377])).

cnf(c_0_381,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_370,c_0_379]),c_0_380]),c_0_377])).

cnf(c_0_382,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_371,c_0_381]),c_0_377])).

cnf(c_0_383,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_354,c_0_369])).

cnf(c_0_384,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_355,c_0_369])).

cnf(c_0_385,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_360,c_0_382])).

cnf(c_0_386,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_383,c_0_372]),c_0_163])).

cnf(c_0_387,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_384,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_388,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_385,c_0_386])).

cnf(c_0_389,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_387,c_0_388]),c_0_136])).

cnf(c_0_390,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_389]),c_0_372])).

cnf(c_0_391,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_367,c_0_390])).

cnf(c_0_392,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_391,c_0_144]),c_0_43])).

cnf(c_0_393,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_392])).

cnf(c_0_394,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_392])).

cnf(c_0_395,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_392])).

cnf(c_0_396,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_393,c_0_100]),c_0_258]),c_0_369]),c_0_394])).

cnf(c_0_397,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_395,c_0_100]),c_0_258]),c_0_369]),c_0_394])).

cnf(c_0_398,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_370,c_0_396]),c_0_397]),c_0_394])).

cnf(c_0_399,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_383,c_0_398]),c_0_394])).

cnf(c_0_400,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_384,c_0_396]),c_0_397]),c_0_394])).

cnf(c_0_401,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_385,c_0_399])).

cnf(c_0_402,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_392])).

cnf(c_0_403,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_400,c_0_401]),c_0_136])).

cnf(c_0_404,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_233,c_0_366])).

cnf(c_0_405,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_402,c_0_403]),c_0_398])).

cnf(c_0_406,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_404,c_0_159])).

cnf(c_0_407,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_237,c_0_405])).

cnf(c_0_408,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_406,c_0_144]),c_0_43]),c_0_102])).

cnf(c_0_409,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_407,c_0_408])).

cnf(c_0_410,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_409])).

cnf(c_0_411,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_410]),c_0_68])])).

cnf(c_0_412,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_411]),c_0_24]),c_0_22])]),c_0_25]),c_0_196]),c_0_369]),c_0_408])).

cnf(c_0_413,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_245,c_0_366])).

cnf(c_0_414,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_412,c_0_244]),c_0_43]),c_0_102])).

cnf(c_0_415,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_413,c_0_159])).

cnf(c_0_416,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_414]),c_0_102])).

cnf(c_0_417,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_249,c_0_405])).

cnf(c_0_418,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_415,c_0_414]),c_0_416])).

cnf(c_0_419,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_417,c_0_408])).

cnf(c_0_420,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_418,c_0_144]),c_0_43]),c_0_102])).

cnf(c_0_421,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_419,c_0_414]),c_0_420])).

cnf(c_0_422,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_409]),c_0_421])).

cnf(c_0_423,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_422]),c_0_68])])).

cnf(c_0_424,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_423]),c_0_24]),c_0_22])]),c_0_25]),c_0_196]),c_0_369]),c_0_408])).

cnf(c_0_425,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_424,c_0_244]),c_0_43]),c_0_102])).

cnf(c_0_426,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_259,c_0_425])).

cnf(c_0_427,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_353,c_0_425])).

cnf(c_0_428,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_426,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_429,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_427,c_0_428]),c_0_163])).

cnf(c_0_430,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_404,c_0_429])).

cnf(c_0_431,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_430,c_0_144]),c_0_43])).

cnf(c_0_432,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_431])).

cnf(c_0_433,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_431])).

cnf(c_0_434,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_431])).

cnf(c_0_435,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_432,c_0_100]),c_0_258]),c_0_425]),c_0_433])).

cnf(c_0_436,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_434,c_0_100]),c_0_258]),c_0_425]),c_0_433])).

cnf(c_0_437,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_426,c_0_435]),c_0_436]),c_0_433])).

cnf(c_0_438,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_427,c_0_437]),c_0_433])).

cnf(c_0_439,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_407,c_0_438])).

cnf(c_0_440,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_439])).

cnf(c_0_441,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_440]),c_0_68])])).

cnf(c_0_442,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_441]),c_0_24]),c_0_22])]),c_0_25]),c_0_234]),c_0_405]),c_0_438])).

cnf(c_0_443,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_442,c_0_244]),c_0_43])).

cnf(c_0_444,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_443])).

cnf(c_0_445,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_443])).

cnf(c_0_446,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_413,c_0_429])).

cnf(c_0_447,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_444,c_0_100]),c_0_258]),c_0_425]),c_0_445])).

cnf(c_0_448,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_417,c_0_438])).

cnf(c_0_449,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_446,c_0_447])).

cnf(c_0_450,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_447]),c_0_43])).

cnf(c_0_451,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_448,c_0_447])).

cnf(c_0_452,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_439])).

cnf(c_0_453,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_449,c_0_144]),c_0_43]),c_0_450])).

cnf(c_0_454,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_451,c_0_452])).

cnf(c_0_455,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_453,c_0_454]),c_0_43])).

cnf(c_0_456,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_455]),c_0_68])])).

cnf(c_0_457,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_456]),c_0_24]),c_0_22])]),c_0_25]),c_0_220]),c_0_392]),c_0_431]),c_0_244])).

cnf(c_0_458,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_457])).

cnf(c_0_459,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_457])).

cnf(c_0_460,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_458,c_0_100]),c_0_258]),c_0_425]),c_0_459])).

cnf(c_0_461,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_443])).

cnf(c_0_462,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_426,c_0_460]),c_0_427])).

cnf(c_0_463,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_461,c_0_100]),c_0_258]),c_0_425]),c_0_445])).

cnf(c_0_464,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_462,c_0_463]),c_0_445])).

cnf(c_0_465,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_446,c_0_464])).

cnf(c_0_466,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_464]),c_0_43])).

cnf(c_0_467,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_448,c_0_464])).

cnf(c_0_468,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_465,c_0_144]),c_0_43]),c_0_466])).

cnf(c_0_469,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_467,c_0_452])).

cnf(c_0_470,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_468,c_0_469]),c_0_43])).

cnf(c_0_471,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_470]),c_0_68])])).

cnf(c_0_472,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_471]),c_0_24]),c_0_22])]),c_0_25]),c_0_220]),c_0_392]),c_0_431]),c_0_244])).

cnf(c_0_473,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_472])).

cnf(c_0_474,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_472])).

cnf(c_0_475,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_473,c_0_100]),c_0_258]),c_0_425]),c_0_474])).

cnf(c_0_476,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_462,c_0_475]),c_0_474])).

cnf(c_0_477,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_354,c_0_425])).

cnf(c_0_478,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_355,c_0_425])).

cnf(c_0_479,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_360,c_0_476])).

cnf(c_0_480,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_477,c_0_428]),c_0_163])).

cnf(c_0_481,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_478,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_482,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_479,c_0_480])).

cnf(c_0_483,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_481,c_0_482]),c_0_136])).

cnf(c_0_484,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_483]),c_0_428])).

cnf(c_0_485,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_404,c_0_484])).

cnf(c_0_486,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_485,c_0_144]),c_0_43])).

cnf(c_0_487,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_486])).

cnf(c_0_488,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_486])).

cnf(c_0_489,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_486])).

cnf(c_0_490,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_487,c_0_100]),c_0_258]),c_0_425]),c_0_488])).

cnf(c_0_491,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_489,c_0_100]),c_0_258]),c_0_425]),c_0_488])).

cnf(c_0_492,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_426,c_0_490]),c_0_491]),c_0_488])).

cnf(c_0_493,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_477,c_0_492]),c_0_488])).

cnf(c_0_494,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_478,c_0_490]),c_0_491]),c_0_488])).

cnf(c_0_495,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_479,c_0_493])).

cnf(c_0_496,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_486])).

cnf(c_0_497,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_494,c_0_495]),c_0_136])).

cnf(c_0_498,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_496,c_0_497]),c_0_492])).

cnf(c_0_499,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_407,c_0_498])).

cnf(c_0_500,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_499])).

cnf(c_0_501,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_500]),c_0_68])])).

cnf(c_0_502,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_501]),c_0_24]),c_0_22])]),c_0_25]),c_0_234]),c_0_405]),c_0_498])).

cnf(c_0_503,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_502,c_0_244]),c_0_43])).

cnf(c_0_504,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_503])).

cnf(c_0_505,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_503])).

cnf(c_0_506,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_413,c_0_484])).

cnf(c_0_507,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_504,c_0_100]),c_0_258]),c_0_425]),c_0_505])).

cnf(c_0_508,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_417,c_0_498])).

cnf(c_0_509,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_506,c_0_507])).

cnf(c_0_510,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_507]),c_0_43])).

cnf(c_0_511,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_508,c_0_507])).

cnf(c_0_512,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_499])).

cnf(c_0_513,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_509,c_0_144]),c_0_43]),c_0_510])).

cnf(c_0_514,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_511,c_0_512])).

cnf(c_0_515,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_513,c_0_514]),c_0_43])).

cnf(c_0_516,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_515]),c_0_68])])).

cnf(c_0_517,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_516]),c_0_24]),c_0_22])]),c_0_25]),c_0_220]),c_0_392]),c_0_486]),c_0_244])).

cnf(c_0_518,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_517])).

cnf(c_0_519,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_517])).

cnf(c_0_520,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_518,c_0_100]),c_0_258]),c_0_425]),c_0_519])).

cnf(c_0_521,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_503])).

cnf(c_0_522,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_426,c_0_520])).

cnf(c_0_523,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_521,c_0_100]),c_0_258]),c_0_425]),c_0_505])).

cnf(c_0_524,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_522,c_0_523]),c_0_505])).

cnf(c_0_525,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_477,c_0_524]),c_0_505])).

cnf(c_0_526,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_506,c_0_525])).

cnf(c_0_527,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_525]),c_0_43])).

cnf(c_0_528,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_508,c_0_525])).

cnf(c_0_529,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_526,c_0_144]),c_0_43]),c_0_527])).

cnf(c_0_530,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_528,c_0_512])).

cnf(c_0_531,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_529,c_0_530]),c_0_43])).

cnf(c_0_532,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_531]),c_0_68])])).

cnf(c_0_533,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_532]),c_0_24]),c_0_22])]),c_0_25]),c_0_220]),c_0_392]),c_0_486]),c_0_244])).

cnf(c_0_534,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_533])).

cnf(c_0_535,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_533])).

cnf(c_0_536,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_220])).

cnf(c_0_537,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_534,c_0_100]),c_0_258]),c_0_425]),c_0_535])).

cnf(c_0_538,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ v7_waybel_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_536])).

cnf(c_0_539,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_392])).

cnf(c_0_540,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_522,c_0_537]),c_0_535])).

cnf(c_0_541,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_538,c_0_539])).

cnf(c_0_542,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_486])).

cnf(c_0_543,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))
    | ~ r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_478,c_0_520])).

cnf(c_0_544,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_477,c_0_540]),c_0_535])).

cnf(c_0_545,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_541,c_0_542])).

cnf(c_0_546,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_543,c_0_523]),c_0_505])).

cnf(c_0_547,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_479,c_0_544])).

cnf(c_0_548,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_536])).

cnf(c_0_549,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_545])).

cnf(c_0_550,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_503])).

cnf(c_0_551,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_546,c_0_547]),c_0_136])).

cnf(c_0_552,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_548,c_0_539])).

cnf(c_0_553,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_549]),c_0_68])])).

cnf(c_0_554,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_550,c_0_551]),c_0_524])).

cnf(c_0_555,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_552,c_0_542])).

cnf(c_0_556,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_553]),c_0_24]),c_0_22])]),c_0_25]),c_0_536]),c_0_539]),c_0_542]),c_0_74])).

cnf(c_0_557,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_506,c_0_554])).

cnf(c_0_558,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_554]),c_0_43])).

cnf(c_0_559,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_508,c_0_554])).

cnf(c_0_560,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_555,c_0_556])).

cnf(c_0_561,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_545])).

cnf(c_0_562,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_557,c_0_144]),c_0_43]),c_0_558])).

cnf(c_0_563,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_559,c_0_512])).

cnf(c_0_564,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_560,c_0_561])).

cnf(c_0_565,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_562,c_0_563]),c_0_43])).

cnf(c_0_566,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_562,c_0_564]),c_0_30])).

cnf(c_0_567,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_565]),c_0_68])])).

cnf(c_0_568,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_566]),c_0_68])])).

cnf(c_0_569,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_567]),c_0_24]),c_0_22])]),c_0_25]),c_0_220]),c_0_392]),c_0_486]),c_0_244])).

cnf(c_0_570,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_568]),c_0_24]),c_0_22])]),c_0_25]),c_0_536]),c_0_539]),c_0_542]),c_0_74])).

cnf(c_0_571,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_569])).

cnf(c_0_572,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_569])).

cnf(c_0_573,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_570]),c_0_258]),c_0_425]),c_0_571])).

cnf(c_0_574,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_518,c_0_570]),c_0_258]),c_0_425]),c_0_519])).

cnf(c_0_575,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_572,c_0_570]),c_0_258]),c_0_425]),c_0_571])).

cnf(c_0_576,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_573,c_0_574]),c_0_575])).

cnf(c_0_577,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_570]),c_0_258]),c_0_425]),c_0_571])).

cnf(c_0_578,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_579,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_569])).

cnf(c_0_580,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_576,c_0_547]),c_0_136])).

cnf(c_0_581,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_577,c_0_574]),c_0_575])).

cnf(c_0_582,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m2_yellow_6(X2,esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_struct_0(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_578,c_0_29]),c_0_25])).

cnf(c_0_583,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_579,c_0_580]),c_0_581])).

cnf(c_0_584,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_582,c_0_583])).

cnf(c_0_585,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_584,c_0_100])).

cnf(c_0_586,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_585,c_0_108]),c_0_109]),c_0_123]),c_0_110])).

cnf(c_0_587,negated_conjecture,
    ( v4_orders_2(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_586])).

cnf(c_0_588,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v4_orders_2(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_587,c_0_141]),c_0_142])).

cnf(c_0_589,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_586]),c_0_32]),c_0_33]),c_0_43])).

cnf(c_0_590,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_588,c_0_589]),c_0_43]),c_0_101])).

cnf(c_0_591,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_590])).

cnf(c_0_592,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_585,c_0_590])).

cnf(c_0_593,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_591,c_0_147]),c_0_148])).

cnf(c_0_594,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_592,c_0_147]),c_0_148])).

cnf(c_0_595,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_593,c_0_153]),c_0_154]),c_0_594])).

cnf(c_0_596,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_587,c_0_595])).

cnf(c_0_597,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_596,c_0_159])).

cnf(c_0_598,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_597,c_0_589]),c_0_43]),c_0_102])).

cnf(c_0_599,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_591,c_0_598])).

cnf(c_0_600,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_592,c_0_598])).

cnf(c_0_601,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_599,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_602,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_600,c_0_601]),c_0_163])).

cnf(c_0_603,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_596,c_0_602])).

cnf(c_0_604,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_603,c_0_589]),c_0_43])).

cnf(c_0_605,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_604])).

cnf(c_0_606,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_604])).

cnf(c_0_607,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_604])).

cnf(c_0_608,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_605,c_0_100]),c_0_590]),c_0_598]),c_0_606])).

cnf(c_0_609,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_607,c_0_100]),c_0_590]),c_0_598]),c_0_606])).

cnf(c_0_610,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_599,c_0_608]),c_0_609]),c_0_606])).

cnf(c_0_611,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_586])).

cnf(c_0_612,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_586])).

cnf(c_0_613,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_600,c_0_610]),c_0_606])).

cnf(c_0_614,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v7_waybel_0(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_611,c_0_141]),c_0_142])).

cnf(c_0_615,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_612,c_0_141]),c_0_142])).

cnf(c_0_616,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ v7_waybel_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_613])).

cnf(c_0_617,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_614,c_0_589]),c_0_43]),c_0_101])).

cnf(c_0_618,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_615,c_0_589]),c_0_43]),c_0_101])).

cnf(c_0_619,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_616,c_0_617]),c_0_618])).

cnf(c_0_620,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_619])).

cnf(c_0_621,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_620]),c_0_68])])).

cnf(c_0_622,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_621]),c_0_24]),c_0_22])]),c_0_25]),c_0_590]),c_0_617]),c_0_618])).

cnf(c_0_623,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_586]),c_0_32]),c_0_33]),c_0_43])).

cnf(c_0_624,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_586])).

cnf(c_0_625,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_622,c_0_623]),c_0_43]),c_0_101])).

cnf(c_0_626,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_624,c_0_141]),c_0_142])).

cnf(c_0_627,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_625]),c_0_101])).

cnf(c_0_628,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_613])).

cnf(c_0_629,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_619])).

cnf(c_0_630,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_626,c_0_625]),c_0_627])).

cnf(c_0_631,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_628,c_0_617]),c_0_629]),c_0_618])).

cnf(c_0_632,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_619])).

cnf(c_0_633,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_630,c_0_589]),c_0_43]),c_0_101])).

cnf(c_0_634,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_631,c_0_632]),c_0_633])).

cnf(c_0_635,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_634]),c_0_68])])).

cnf(c_0_636,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_635]),c_0_24]),c_0_22])]),c_0_25]),c_0_590]),c_0_617]),c_0_618])).

cnf(c_0_637,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_636,c_0_623]),c_0_43]),c_0_101])).

cnf(c_0_638,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_637])).

cnf(c_0_639,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_585,c_0_637])).

cnf(c_0_640,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_638,c_0_147]),c_0_148])).

cnf(c_0_641,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_639,c_0_147]),c_0_148])).

cnf(c_0_642,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_640,c_0_153]),c_0_154]),c_0_641])).

cnf(c_0_643,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_611,c_0_642])).

cnf(c_0_644,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v7_waybel_0(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_643,c_0_159])).

cnf(c_0_645,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_644,c_0_589]),c_0_43]),c_0_102])).

cnf(c_0_646,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_638,c_0_645])).

cnf(c_0_647,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_639,c_0_645])).

cnf(c_0_648,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_646,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_649,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_647,c_0_648]),c_0_163])).

cnf(c_0_650,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v7_waybel_0(X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_643,c_0_649])).

cnf(c_0_651,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_650,c_0_589]),c_0_43])).

cnf(c_0_652,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_651])).

cnf(c_0_653,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_651])).

cnf(c_0_654,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_651])).

cnf(c_0_655,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_652,c_0_100]),c_0_637]),c_0_645]),c_0_653])).

cnf(c_0_656,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_654,c_0_100]),c_0_637]),c_0_645]),c_0_653])).

cnf(c_0_657,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_646,c_0_655]),c_0_656]),c_0_653])).

cnf(c_0_658,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_612,c_0_642])).

cnf(c_0_659,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_647,c_0_657]),c_0_653])).

cnf(c_0_660,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_658,c_0_159])).

cnf(c_0_661,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_616,c_0_659])).

cnf(c_0_662,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_660,c_0_589]),c_0_43]),c_0_102])).

cnf(c_0_663,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_661,c_0_662])).

cnf(c_0_664,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_663])).

cnf(c_0_665,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_664]),c_0_68])])).

cnf(c_0_666,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_665]),c_0_24]),c_0_22])]),c_0_25]),c_0_598]),c_0_645]),c_0_662])).

cnf(c_0_667,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_624,c_0_642])).

cnf(c_0_668,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_666,c_0_623]),c_0_43]),c_0_102])).

cnf(c_0_669,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_667,c_0_159])).

cnf(c_0_670,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_668]),c_0_102])).

cnf(c_0_671,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_628,c_0_659])).

cnf(c_0_672,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_669,c_0_668]),c_0_670])).

cnf(c_0_673,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_671,c_0_662])).

cnf(c_0_674,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_672,c_0_589]),c_0_43]),c_0_102])).

cnf(c_0_675,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_673,c_0_668]),c_0_674])).

cnf(c_0_676,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_663])).

cnf(c_0_677,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_675,c_0_676])).

cnf(c_0_678,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_677]),c_0_68])])).

cnf(c_0_679,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_678]),c_0_24]),c_0_22])]),c_0_25]),c_0_598]),c_0_645]),c_0_662])).

cnf(c_0_680,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_679,c_0_623]),c_0_43]),c_0_102])).

cnf(c_0_681,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_638,c_0_680])).

cnf(c_0_682,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_639,c_0_680])).

cnf(c_0_683,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_681,c_0_166]),c_0_167]),c_0_163])).

cnf(c_0_684,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_682,c_0_683]),c_0_163])).

cnf(c_0_685,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_658,c_0_684])).

cnf(c_0_686,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_685,c_0_589]),c_0_43])).

cnf(c_0_687,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_686])).

cnf(c_0_688,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_686])).

cnf(c_0_689,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_686])).

cnf(c_0_690,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_687,c_0_100]),c_0_637]),c_0_680]),c_0_688])).

cnf(c_0_691,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_689,c_0_100]),c_0_637]),c_0_680]),c_0_688])).

cnf(c_0_692,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_681,c_0_690]),c_0_691]),c_0_688])).

cnf(c_0_693,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_682,c_0_692]),c_0_688])).

cnf(c_0_694,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_661,c_0_693])).

cnf(c_0_695,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_694])).

cnf(c_0_696,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_695]),c_0_68])])).

cnf(c_0_697,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_696]),c_0_24]),c_0_22])]),c_0_25]),c_0_613]),c_0_659]),c_0_693])).

cnf(c_0_698,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_697,c_0_623]),c_0_43])).

cnf(c_0_699,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_698])).

cnf(c_0_700,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_698])).

cnf(c_0_701,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X2,X1)
    | ~ m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_667,c_0_684])).

cnf(c_0_702,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_699,c_0_100]),c_0_637]),c_0_680]),c_0_700])).

cnf(c_0_703,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_671,c_0_693])).

cnf(c_0_704,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_701,c_0_702])).

cnf(c_0_705,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_702]),c_0_43])).

cnf(c_0_706,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_703,c_0_702])).

cnf(c_0_707,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_694])).

cnf(c_0_708,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_704,c_0_589]),c_0_43]),c_0_705])).

cnf(c_0_709,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_706,c_0_707])).

cnf(c_0_710,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_708,c_0_709]),c_0_43])).

cnf(c_0_711,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_710]),c_0_68])])).

cnf(c_0_712,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_711]),c_0_24]),c_0_22])]),c_0_25]),c_0_604]),c_0_651]),c_0_686]),c_0_623])).

cnf(c_0_713,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_712])).

cnf(c_0_714,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_712])).

cnf(c_0_715,negated_conjecture,
    ( v4_orders_2(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_604])).

cnf(c_0_716,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_713,c_0_100]),c_0_637]),c_0_680]),c_0_714])).

cnf(c_0_717,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_698])).

cnf(c_0_718,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ v7_waybel_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_715])).

cnf(c_0_719,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_651])).

cnf(c_0_720,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_681,c_0_716]),c_0_682])).

cnf(c_0_721,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_717,c_0_100]),c_0_637]),c_0_680]),c_0_700])).

cnf(c_0_722,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_718,c_0_719])).

cnf(c_0_723,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_686])).

cnf(c_0_724,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_720,c_0_721]),c_0_700])).

cnf(c_0_725,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ v7_waybel_0(esk8_1(esk5_1(esk6_0)))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_715])).

cnf(c_0_726,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_722,c_0_723])).

cnf(c_0_727,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | ~ m2_yellow_6(X1,esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_701,c_0_724])).

cnf(c_0_728,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_724]),c_0_43])).

cnf(c_0_729,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_703,c_0_724])).

cnf(c_0_730,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_725,c_0_719])).

cnf(c_0_731,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_726])).

cnf(c_0_732,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_727,c_0_589]),c_0_43]),c_0_728])).

cnf(c_0_733,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_729,c_0_707])).

cnf(c_0_734,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_730,c_0_723]),c_0_731])).

cnf(c_0_735,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_726])).

cnf(c_0_736,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_732,c_0_733]),c_0_43])).

cnf(c_0_737,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_734,c_0_735])).

cnf(c_0_738,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_736]),c_0_68])])).

cnf(c_0_739,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_732,c_0_737]),c_0_30])).

cnf(c_0_740,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_738]),c_0_24]),c_0_22])]),c_0_25]),c_0_604]),c_0_651]),c_0_686]),c_0_623])).

cnf(c_0_741,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))) = k1_xboole_0
    | v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_739]),c_0_68])])).

cnf(c_0_742,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_740])).

cnf(c_0_743,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_741]),c_0_24]),c_0_22])]),c_0_25]),c_0_715]),c_0_719]),c_0_723]),c_0_74])).

cnf(c_0_744,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_740])).

cnf(c_0_745,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_742,c_0_743]),c_0_637]),c_0_680]),c_0_744])).

cnf(c_0_746,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_720,c_0_745]),c_0_744])).

cnf(c_0_747,negated_conjecture,
    ( v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_570]),c_0_258]),c_0_425])).

cnf(c_0_748,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_570]),c_0_258]),c_0_425])).

cnf(c_0_749,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_570]),c_0_258]),c_0_425])).

cnf(c_0_750,negated_conjecture,
    ( v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_582,c_0_746])).

cnf(c_0_751,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_747,c_0_581]),c_0_571])).

cnf(c_0_752,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_748,c_0_581]),c_0_571])).

cnf(c_0_753,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_749,c_0_581]),c_0_571])).

cnf(c_0_754,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_750,c_0_39]),c_0_40]),c_0_41]),c_0_50])).

cnf(c_0_755,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_751]),c_0_752]),c_0_753])).

cnf(c_0_756,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_754])).

cnf(c_0_757,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_576,c_0_755]),c_0_136])).

cnf(c_0_758,negated_conjecture,
    ( v4_orders_2(X1)
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_754])).

cnf(c_0_759,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_756,c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_760,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_754]),c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_761,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_754]),c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_762,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_754])).

cnf(c_0_763,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_754])).

cnf(c_0_764,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_579,c_0_757]),c_0_581])).

cnf(c_0_765,negated_conjecture,
    ( v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_754])).

cnf(c_0_766,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v4_orders_2(X1)
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_758,c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_767,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_759,c_0_760]),c_0_761])).

cnf(c_0_768,negated_conjecture,
    ( v7_waybel_0(X1)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_762,c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_769,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_763,c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_770,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_582,c_0_764])).

cnf(c_0_771,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_743]),c_0_637]),c_0_680]),c_0_744])).

cnf(c_0_772,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_713,c_0_743]),c_0_637]),c_0_680]),c_0_714])).

cnf(c_0_773,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_765,c_0_108]),c_0_109]),c_0_110])).

cnf(c_0_774,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_766,c_0_767])).

cnf(c_0_775,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_768,c_0_767])).

cnf(c_0_776,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_769,c_0_767])).

cnf(c_0_777,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0)))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_770,c_0_743]),c_0_637]),c_0_680])).

cnf(c_0_778,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_771,c_0_772]),c_0_745])).

cnf(c_0_779,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_773,c_0_760]),c_0_761])).

cnf(c_0_780,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_774]),c_0_775]),c_0_776])).

cnf(c_0_781,negated_conjecture,
    ( v2_struct_0(esk8_1(esk5_1(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_777,c_0_778]),c_0_744])).

cnf(c_0_782,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_779,c_0_780]),c_0_136])).

cnf(c_0_783,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_582,c_0_781])).

cnf(c_0_784,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_782]),c_0_767])).

cnf(c_0_785,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_783,c_0_784])).

cnf(c_0_786,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_785,c_0_141]),c_0_142])).

cnf(c_0_787,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_784]),c_0_32]),c_0_33]),c_0_43])).

cnf(c_0_788,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_786,c_0_787]),c_0_43]),c_0_101])).

cnf(c_0_789,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_756,c_0_788])).

cnf(c_0_790,negated_conjecture,
    ( v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_758,c_0_788])).

cnf(c_0_791,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_789,c_0_147]),c_0_148])).

cnf(c_0_792,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_754]),c_0_141]),c_0_147]),c_0_148])).

cnf(c_0_793,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_754]),c_0_141]),c_0_147]),c_0_148])).

cnf(c_0_794,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_790,c_0_147]),c_0_148])).

cnf(c_0_795,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_791,c_0_792]),c_0_793])).

cnf(c_0_796,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_794,c_0_795])).

cnf(c_0_797,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_785,c_0_796])).

cnf(c_0_798,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_797,c_0_159])).

cnf(c_0_799,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_798,c_0_787]),c_0_43]),c_0_102])).

cnf(c_0_800,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_789,c_0_799])).

cnf(c_0_801,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_754]),c_0_142]),c_0_159]),c_0_163])).

cnf(c_0_802,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_754]),c_0_142]),c_0_159]),c_0_163])).

cnf(c_0_803,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_790,c_0_799])).

cnf(c_0_804,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_800,c_0_801]),c_0_802]),c_0_163])).

cnf(c_0_805,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_803,c_0_804]),c_0_163])).

cnf(c_0_806,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_797,c_0_805])).

cnf(c_0_807,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_806,c_0_787]),c_0_43])).

cnf(c_0_808,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_807])).

cnf(c_0_809,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_807])).

cnf(c_0_810,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_807])).

cnf(c_0_811,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_808,c_0_754]),c_0_788]),c_0_799]),c_0_809])).

cnf(c_0_812,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_810,c_0_754]),c_0_788]),c_0_799]),c_0_809])).

cnf(c_0_813,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_800,c_0_811]),c_0_812]),c_0_809])).

cnf(c_0_814,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_762,c_0_788])).

cnf(c_0_815,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_763,c_0_788])).

cnf(c_0_816,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_765,c_0_788])).

cnf(c_0_817,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_803,c_0_813]),c_0_809])).

cnf(c_0_818,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_814,c_0_147]),c_0_148])).

cnf(c_0_819,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_815,c_0_147]),c_0_148])).

cnf(c_0_820,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_816,c_0_147]),c_0_148])).

cnf(c_0_821,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | ~ v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_128,c_0_817])).

cnf(c_0_822,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_818,c_0_795])).

cnf(c_0_823,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_819,c_0_795])).

cnf(c_0_824,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_820,c_0_792]),c_0_793])).

cnf(c_0_825,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_821,c_0_822]),c_0_823])).

cnf(c_0_826,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_824,c_0_825]),c_0_136])).

cnf(c_0_827,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_826]),c_0_795])).

cnf(c_0_828,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_785,c_0_827])).

cnf(c_0_829,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_828,c_0_159])).

cnf(c_0_830,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_829,c_0_787]),c_0_43]),c_0_102])).

cnf(c_0_831,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_789,c_0_830])).

cnf(c_0_832,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_814,c_0_830])).

cnf(c_0_833,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_831,c_0_801]),c_0_802]),c_0_163])).

cnf(c_0_834,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_832,c_0_833]),c_0_163])).

cnf(c_0_835,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_828,c_0_834])).

cnf(c_0_836,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_835,c_0_787]),c_0_43])).

cnf(c_0_837,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_836])).

cnf(c_0_838,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_836])).

cnf(c_0_839,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_836])).

cnf(c_0_840,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_837,c_0_754]),c_0_788]),c_0_830]),c_0_838])).

cnf(c_0_841,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_839,c_0_754]),c_0_788]),c_0_830]),c_0_838])).

cnf(c_0_842,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_831,c_0_840]),c_0_841]),c_0_838])).

cnf(c_0_843,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_832,c_0_842]),c_0_838])).

cnf(c_0_844,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_815,c_0_830])).

cnf(c_0_845,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_816,c_0_830])).

cnf(c_0_846,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_821,c_0_843])).

cnf(c_0_847,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_844,c_0_833]),c_0_163])).

cnf(c_0_848,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_845,c_0_801]),c_0_802]),c_0_163])).

cnf(c_0_849,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_846,c_0_847])).

cnf(c_0_850,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_848,c_0_849]),c_0_136])).

cnf(c_0_851,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_850]),c_0_833])).

cnf(c_0_852,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_828,c_0_851])).

cnf(c_0_853,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_852,c_0_787]),c_0_43])).

cnf(c_0_854,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_853])).

cnf(c_0_855,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | ~ v2_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_853])).

cnf(c_0_856,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_853])).

cnf(c_0_857,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_853])).

cnf(c_0_858,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_854]),c_0_788]),c_0_830]),c_0_855])).

cnf(c_0_859,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_856,c_0_854]),c_0_788]),c_0_830]),c_0_855])).

cnf(c_0_860,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_857,c_0_854]),c_0_788]),c_0_830]),c_0_855])).

cnf(c_0_861,negated_conjecture,
    ( l1_waybel_0(X1,esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_854]),c_0_788]),c_0_830]),c_0_855])).

cnf(c_0_862,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_858,c_0_859]),c_0_860])).

cnf(c_0_863,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_854]),c_0_788]),c_0_830]),c_0_855])).

cnf(c_0_864,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_861,c_0_862])).

cnf(c_0_865,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_863,c_0_859]),c_0_860])).

cnf(c_0_866,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_846,c_0_864])).

cnf(c_0_867,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | ~ v3_yellow_6(X1,esk6_0)
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_853])).

cnf(c_0_868,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_865,c_0_866]),c_0_136])).

cnf(c_0_869,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_867,c_0_868]),c_0_862])).

cnf(c_0_870,negated_conjecture,
    ( v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(X1)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_582,c_0_869])).

cnf(c_0_871,negated_conjecture,
    ( v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ v7_waybel_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_870,c_0_754])).

cnf(c_0_872,negated_conjecture,
    ( v4_orders_2(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_871,c_0_108]),c_0_109]),c_0_767]),c_0_110])).

cnf(c_0_873,negated_conjecture,
    ( v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | ~ v7_waybel_0(esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_783,c_0_872])).

cnf(c_0_874,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_873,c_0_141]),c_0_142])).

cnf(c_0_875,negated_conjecture,
    ( v1_compts_1(esk6_0)
    | m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_872]),c_0_32]),c_0_33]),c_0_43])).

cnf(c_0_876,negated_conjecture,
    ( v7_waybel_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_874,c_0_875]),c_0_43]),c_0_101])).

cnf(c_0_877,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ l1_waybel_0(esk7_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_756,c_0_876])])).

cnf(c_0_878,negated_conjecture,
    ( v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | ~ l1_waybel_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_871,c_0_876])])).

cnf(c_0_879,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_877,c_0_147]),c_0_148])).

cnf(c_0_880,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_878,c_0_147]),c_0_148])).

cnf(c_0_881,negated_conjecture,
    ( v7_waybel_0(esk5_1(esk6_0))
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_879,c_0_792]),c_0_793]),c_0_880])).

cnf(c_0_882,negated_conjecture,
    ( v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))
    | ~ l1_waybel_0(esk5_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_873,c_0_881])).

cnf(c_0_883,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0)
    | v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_882,c_0_159])).

cnf(c_0_884,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_883,c_0_875]),c_0_43]),c_0_102])).

cnf(c_0_885,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_877,c_0_884])])).

cnf(c_0_886,negated_conjecture,
    ( v4_orders_2(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_854]),c_0_788]),c_0_830]),c_0_855])).

cnf(c_0_887,negated_conjecture,
    ( v7_waybel_0(X1)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | ~ m2_yellow_6(X1,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_854]),c_0_788]),c_0_830]),c_0_855])).

cnf(c_0_888,negated_conjecture,
    ( v2_struct_0(esk5_1(esk6_0))
    | v2_struct_0(esk7_0)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_878,c_0_884])])).

cnf(c_0_889,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)
    | l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_885,c_0_801]),c_0_802]),c_0_163])).

cnf(c_0_890,negated_conjecture,
    ( v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_886,c_0_862])).

cnf(c_0_891,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_887,c_0_862])).

cnf(c_0_892,negated_conjecture,
    ( l1_waybel_0(esk5_1(esk6_0),esk6_0)
    | v2_struct_0(esk5_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_888,c_0_889]),c_0_163])).

cnf(c_0_893,negated_conjecture,
    ( k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) = k1_xboole_0
    | v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_890]),c_0_891]),c_0_864])).

cnf(c_0_894,negated_conjecture,
    ( v2_struct_0(esk5_1(esk6_0))
    | ~ m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_882,c_0_892])).

cnf(c_0_895,negated_conjecture,
    ( v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)
    | v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_865,c_0_893]),c_0_136])).

cnf(c_0_896,negated_conjecture,
    ( v1_compts_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_894,c_0_875]),c_0_43])).

cnf(c_0_897,negated_conjecture,
    ( v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_867,c_0_895]),c_0_862])).

cnf(c_0_898,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_896])])).

cnf(c_0_899,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_896])])).

cnf(c_0_900,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_896])])).

cnf(c_0_901,negated_conjecture,
    ( r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_896])])).

cnf(c_0_902,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,X1)
    | ~ l1_waybel_0(X1,esk6_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_582,c_0_897])).

cnf(c_0_903,negated_conjecture,
    ( m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)
    | ~ r3_waybel_9(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_898]),c_0_884]),c_0_876])]),c_0_899])).

cnf(c_0_904,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_900,c_0_898]),c_0_884]),c_0_876])]),c_0_899])).

cnf(c_0_905,negated_conjecture,
    ( r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_901,c_0_898]),c_0_884]),c_0_876])]),c_0_899])).

cnf(c_0_906,negated_conjecture,
    ( ~ m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_902,c_0_898]),c_0_884]),c_0_876])]),c_0_899])).

cnf(c_0_907,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_903,c_0_904]),c_0_905])]),c_0_906]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 12.47/12.64  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 12.47/12.64  # and selection function SelectCQIArEqFirst.
% 12.47/12.64  #
% 12.47/12.64  # Preprocessing time       : 0.029 s
% 12.47/12.64  # Presaturation interreduction done
% 12.47/12.64  
% 12.47/12.64  # Proof found!
% 12.47/12.64  # SZS status Theorem
% 12.47/12.64  # SZS output start CNFRefutation
% 12.47/12.64  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow19)).
% 12.47/12.64  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.47/12.64  fof(t36_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>~((r2_hidden(X2,k6_yellow_6(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r3_waybel_9(X1,X2,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_yellow19)).
% 12.47/12.64  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 12.47/12.64  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 12.47/12.64  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 12.47/12.64  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 12.47/12.64  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.47/12.64  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.47/12.64  fof(t31_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_waybel_9)).
% 12.47/12.64  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_yellow_6)).
% 12.47/12.64  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_waybel_9)).
% 12.47/12.64  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 12.47/12.64  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 12.47/12.64  fof(l37_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l37_yellow19)).
% 12.47/12.64  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 12.47/12.64  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 12.47/12.64  fof(c_0_17, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 12.47/12.64  fof(c_0_18, negated_conjecture, ![X47, X48]:(((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&((((((~v2_struct_0(esk7_0)|~v1_compts_1(esk6_0))&(v4_orders_2(esk7_0)|~v1_compts_1(esk6_0)))&(v7_waybel_0(esk7_0)|~v1_compts_1(esk6_0)))&(l1_waybel_0(esk7_0,esk6_0)|~v1_compts_1(esk6_0)))&(~m2_yellow_6(X47,esk6_0,esk7_0)|~v3_yellow_6(X47,esk6_0)|~v1_compts_1(esk6_0)))&((m2_yellow_6(esk8_1(X48),esk6_0,X48)|(v2_struct_0(X48)|~v4_orders_2(X48)|~v7_waybel_0(X48)|~l1_waybel_0(X48,esk6_0))|v1_compts_1(esk6_0))&(v3_yellow_6(esk8_1(X48),esk6_0)|(v2_struct_0(X48)|~v4_orders_2(X48)|~v7_waybel_0(X48)|~l1_waybel_0(X48,esk6_0))|v1_compts_1(esk6_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).
% 12.47/12.64  fof(c_0_19, plain, ![X40, X41, X44]:(((m1_subset_1(esk4_2(X40,X41),u1_struct_0(X40))|~r2_hidden(X41,k6_yellow_6(X40))|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X40))|~v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(r3_waybel_9(X40,X41,esk4_2(X40,X41))|~r2_hidden(X41,k6_yellow_6(X40))|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X40))|~v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(((((~v2_struct_0(esk5_1(X40))|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(v4_orders_2(esk5_1(X40))|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(v7_waybel_0(esk5_1(X40))|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(l1_waybel_0(esk5_1(X40),X40)|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&((r2_hidden(esk5_1(X40),k6_yellow_6(X40))|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(~m1_subset_1(X44,u1_struct_0(X40))|~r3_waybel_9(X40,esk5_1(X40),X44)|v1_compts_1(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_yellow19])])])])])])).
% 12.47/12.64  fof(c_0_20, plain, ![X21, X22, X23]:((((~v2_struct_0(X23)|~m2_yellow_6(X23,X21,X22)|(v2_struct_0(X21)|~l1_struct_0(X21)|v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21)))&(v4_orders_2(X23)|~m2_yellow_6(X23,X21,X22)|(v2_struct_0(X21)|~l1_struct_0(X21)|v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))))&(v7_waybel_0(X23)|~m2_yellow_6(X23,X21,X22)|(v2_struct_0(X21)|~l1_struct_0(X21)|v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))))&(l1_waybel_0(X23,X21)|~m2_yellow_6(X23,X21,X22)|(v2_struct_0(X21)|~l1_struct_0(X21)|v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 12.47/12.64  cnf(c_0_21, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 12.47/12.64  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  cnf(c_0_23, plain, (v4_orders_2(esk5_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.47/12.64  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  cnf(c_0_26, plain, (v7_waybel_0(esk5_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.47/12.64  cnf(c_0_27, plain, (l1_waybel_0(esk5_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.47/12.64  cnf(c_0_28, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 12.47/12.64  cnf(c_0_29, negated_conjecture, (l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 12.47/12.64  cnf(c_0_30, negated_conjecture, (v4_orders_2(esk7_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  cnf(c_0_31, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_32, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_33, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_34, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk5_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.47/12.64  cnf(c_0_35, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 12.47/12.64  cnf(c_0_36, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 12.47/12.64  fof(c_0_37, plain, ![X19, X20]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19)|m1_subset_1(k10_yellow_6(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 12.47/12.64  cnf(c_0_38, negated_conjecture, (v4_orders_2(X1)|v2_struct_0(X2)|~m2_yellow_6(X1,esk6_0,X2)|~l1_waybel_0(X2,esk6_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_25])).
% 12.47/12.64  cnf(c_0_39, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v4_orders_2(esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 12.47/12.64  cnf(c_0_40, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_32])).
% 12.47/12.64  cnf(c_0_41, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 12.47/12.64  cnf(c_0_42, negated_conjecture, (m2_yellow_6(esk8_1(X1),esk6_0,X1)|v2_struct_0(X1)|v1_compts_1(esk6_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  cnf(c_0_43, negated_conjecture, (v1_compts_1(esk6_0)|~v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_44, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(X2)|~m2_yellow_6(X1,esk6_0,X2)|~l1_waybel_0(X2,esk6_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_25])).
% 12.47/12.64  cnf(c_0_45, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(X2)|~m2_yellow_6(X1,esk6_0,X2)|~l1_waybel_0(X2,esk6_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_25])).
% 12.47/12.64  fof(c_0_46, plain, ![X9, X10, X11]:((m1_subset_1(esk1_3(X9,X10,X11),X9)|r1_tarski(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(X9)))&((r2_hidden(esk1_3(X9,X10,X11),X10)|r1_tarski(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(X9)))&(~r2_hidden(esk1_3(X9,X10,X11),X11)|r1_tarski(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 12.47/12.64  fof(c_0_47, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 12.47/12.64  cnf(c_0_48, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 12.47/12.64  cnf(c_0_49, negated_conjecture, (v4_orders_2(esk7_0)|v4_orders_2(X1)|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])).
% 12.47/12.64  cnf(c_0_50, negated_conjecture, (m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|v4_orders_2(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_39]), c_0_40]), c_0_41]), c_0_43]), c_0_30])).
% 12.47/12.64  cnf(c_0_51, negated_conjecture, (v7_waybel_0(X1)|v4_orders_2(esk7_0)|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_39]), c_0_40]), c_0_41])).
% 12.47/12.64  cnf(c_0_52, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v4_orders_2(esk7_0)|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_39]), c_0_40]), c_0_41])).
% 12.47/12.64  cnf(c_0_53, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 12.47/12.64  cnf(c_0_54, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 12.47/12.64  cnf(c_0_55, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k10_yellow_6(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_56, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk7_0)|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 12.47/12.64  cnf(c_0_57, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk7_0)|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 12.47/12.64  cnf(c_0_58, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk7_0)|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_52, c_0_50])).
% 12.47/12.64  fof(c_0_59, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 12.47/12.64  cnf(c_0_60, plain, (m1_subset_1(esk1_3(X1,X2,k1_xboole_0),X1)|r1_tarski(X2,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 12.47/12.64  cnf(c_0_61, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])).
% 12.47/12.64  fof(c_0_62, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 12.47/12.64  cnf(c_0_63, negated_conjecture, (v3_yellow_6(esk8_1(X1),esk6_0)|v2_struct_0(X1)|v1_compts_1(esk6_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  fof(c_0_64, plain, ![X29, X30, X31, X32]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(v2_struct_0(X30)|~v4_orders_2(X30)|~v7_waybel_0(X30)|~l1_waybel_0(X30,X29)|(~m2_yellow_6(X31,X29,X30)|(~m1_subset_1(X32,u1_struct_0(X29))|(~r3_waybel_9(X29,X31,X32)|r3_waybel_9(X29,X30,X32)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).
% 12.47/12.64  fof(c_0_65, plain, ![X24, X25]:((~v3_yellow_6(X25,X24)|k10_yellow_6(X24,X25)!=k1_xboole_0|(v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(k10_yellow_6(X24,X25)=k1_xboole_0|v3_yellow_6(X25,X24)|(v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 12.47/12.64  cnf(c_0_66, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 12.47/12.64  cnf(c_0_67, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 12.47/12.64  cnf(c_0_68, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 12.47/12.64  cnf(c_0_69, negated_conjecture, (v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk7_0)|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_39]), c_0_40]), c_0_43]), c_0_30])).
% 12.47/12.64  cnf(c_0_70, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~r3_waybel_9(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 12.47/12.64  cnf(c_0_71, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk5_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 12.47/12.64  cnf(c_0_72, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 12.47/12.64  cnf(c_0_73, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 12.47/12.64  cnf(c_0_74, negated_conjecture, (v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_41])).
% 12.47/12.64  fof(c_0_75, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26)|(~m1_subset_1(X28,u1_struct_0(X26))|(~r2_hidden(X28,k10_yellow_6(X26,X27))|r3_waybel_9(X26,X27,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 12.47/12.64  fof(c_0_76, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|m1_subset_1(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 12.47/12.64  cnf(c_0_77, negated_conjecture, (r3_waybel_9(esk6_0,X1,X2)|v2_struct_0(X1)|~r3_waybel_9(esk6_0,X3,X2)|~m2_yellow_6(X3,esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_78, negated_conjecture, (v1_compts_1(esk6_0)|~r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_79, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_24]), c_0_22])]), c_0_25]), c_0_56]), c_0_57]), c_0_58]), c_0_74])).
% 12.47/12.64  cnf(c_0_80, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 12.47/12.64  cnf(c_0_81, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 12.47/12.64  cnf(c_0_82, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 12.47/12.64  cnf(c_0_83, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v4_orders_2(esk7_0)|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_39]), c_0_40]), c_0_41])).
% 12.47/12.64  cnf(c_0_84, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_43]), c_0_30])).
% 12.47/12.64  cnf(c_0_85, negated_conjecture, (r3_waybel_9(esk6_0,X1,X2)|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~r2_hidden(X2,k10_yellow_6(esk6_0,X1))|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_86, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_81, c_0_61])).
% 12.47/12.64  cnf(c_0_87, plain, (r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2)|r1_tarski(X2,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_82, c_0_54])).
% 12.47/12.64  cnf(c_0_88, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_79]), c_0_84])).
% 12.47/12.64  cnf(c_0_89, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_56]), c_0_86]), c_0_57]), c_0_58])).
% 12.47/12.64  cnf(c_0_90, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_61])).
% 12.47/12.64  cnf(c_0_91, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(spm,[status(thm)],[c_0_88, c_0_50])).
% 12.47/12.64  fof(c_0_92, plain, ![X33, X34, X35]:((m2_yellow_6(esk2_3(X33,X34,X35),X33,X34)|~r3_waybel_9(X33,X34,X35)|~m1_subset_1(X35,u1_struct_0(X33))|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(r2_hidden(X35,k10_yellow_6(X33,esk2_3(X33,X34,X35)))|~r3_waybel_9(X33,X34,X35)|~m1_subset_1(X35,u1_struct_0(X33))|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 12.47/12.64  cnf(c_0_93, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])).
% 12.47/12.64  fof(c_0_94, plain, ![X37, X38]:((m1_subset_1(esk3_2(X37,X38),u1_struct_0(X37))|(v2_struct_0(X38)|~v4_orders_2(X38)|~v7_waybel_0(X38)|~l1_waybel_0(X38,X37))|~v1_compts_1(X37)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(r3_waybel_9(X37,X38,esk3_2(X37,X38))|(v2_struct_0(X38)|~v4_orders_2(X38)|~v7_waybel_0(X38)|~l1_waybel_0(X38,X37))|~v1_compts_1(X37)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).
% 12.47/12.64  cnf(c_0_95, plain, (m2_yellow_6(esk2_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 12.47/12.64  cnf(c_0_96, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_93]), c_0_68])])).
% 12.47/12.64  cnf(c_0_97, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 12.47/12.64  cnf(c_0_98, plain, (r3_waybel_9(X1,X2,esk3_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 12.47/12.64  cnf(c_0_99, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,X1,X2),esk6_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk6_0,X1,X2)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_100, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_96]), c_0_24]), c_0_22])]), c_0_25]), c_0_56]), c_0_57]), c_0_58]), c_0_74])).
% 12.47/12.64  cnf(c_0_101, negated_conjecture, (v7_waybel_0(esk7_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  cnf(c_0_102, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  cnf(c_0_103, negated_conjecture, (~v2_struct_0(esk7_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  cnf(c_0_104, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~v1_compts_1(esk6_0)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_105, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v2_struct_0(X1)|~v1_compts_1(esk6_0)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_106, plain, (r2_hidden(X1,k10_yellow_6(X2,esk2_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 12.47/12.64  cnf(c_0_107, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 12.47/12.64  cnf(c_0_108, negated_conjecture, (v7_waybel_0(esk7_0)|v4_orders_2(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_101, c_0_31])).
% 12.47/12.64  cnf(c_0_109, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_102, c_0_31])).
% 12.47/12.64  cnf(c_0_110, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_31])).
% 12.47/12.64  cnf(c_0_111, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_31])).
% 12.47/12.64  cnf(c_0_112, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_31])).
% 12.47/12.64  cnf(c_0_113, negated_conjecture, (v2_struct_0(X1)|r2_hidden(X2,k10_yellow_6(esk6_0,esk2_3(esk6_0,X1,X2)))|~r3_waybel_9(esk6_0,X1,X2)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_114, negated_conjecture, (v4_orders_2(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_38, c_0_100])).
% 12.47/12.64  cnf(c_0_115, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.64  cnf(c_0_116, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_100]), c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.64  cnf(c_0_117, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_100]), c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.64  cnf(c_0_118, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_100])).
% 12.47/12.64  cnf(c_0_119, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_100])).
% 12.47/12.64  cnf(c_0_120, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_113, c_0_100])).
% 12.47/12.64  cnf(c_0_121, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 12.47/12.64  cnf(c_0_122, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v4_orders_2(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.64  cnf(c_0_123, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])).
% 12.47/12.64  cnf(c_0_124, negated_conjecture, (v7_waybel_0(X1)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.64  cnf(c_0_125, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.64  fof(c_0_126, plain, ![X16, X17]:(~r2_hidden(X16,X17)|~r1_tarski(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 12.47/12.64  cnf(c_0_127, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.64  cnf(c_0_128, negated_conjecture, (k10_yellow_6(esk6_0,X1)=k1_xboole_0|v3_yellow_6(X1,esk6_0)|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_22]), c_0_24])]), c_0_25])).
% 12.47/12.64  cnf(c_0_129, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 12.47/12.64  cnf(c_0_130, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_124, c_0_123])).
% 12.47/12.64  cnf(c_0_131, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_125, c_0_123])).
% 12.47/12.64  cnf(c_0_132, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_126])).
% 12.47/12.64  cnf(c_0_133, negated_conjecture, (~m2_yellow_6(X1,esk6_0,esk7_0)|~v3_yellow_6(X1,esk6_0)|~v1_compts_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.47/12.64  cnf(c_0_134, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_116]), c_0_117])).
% 12.47/12.64  cnf(c_0_135, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130]), c_0_131])).
% 12.47/12.64  cnf(c_0_136, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_132, c_0_68])).
% 12.47/12.64  cnf(c_0_137, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_31])).
% 12.47/12.64  cnf(c_0_138, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_136])).
% 12.47/12.64  cnf(c_0_139, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_123])).
% 12.47/12.64  cnf(c_0_140, negated_conjecture, (v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_139])).
% 12.47/12.64  cnf(c_0_141, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_101, c_0_32])).
% 12.47/12.64  cnf(c_0_142, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_101, c_0_33])).
% 12.47/12.64  cnf(c_0_143, negated_conjecture, (v7_waybel_0(esk7_0)|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_142])).
% 12.47/12.64  cnf(c_0_144, negated_conjecture, (v1_compts_1(esk6_0)|m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_139]), c_0_32]), c_0_33]), c_0_43])).
% 12.47/12.64  cnf(c_0_145, negated_conjecture, (v7_waybel_0(esk7_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_43]), c_0_101])).
% 12.47/12.64  cnf(c_0_146, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_107, c_0_145])).
% 12.47/12.64  cnf(c_0_147, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v7_waybel_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_102, c_0_32])).
% 12.47/12.64  cnf(c_0_148, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_32])).
% 12.47/12.64  cnf(c_0_149, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_32])).
% 12.47/12.64  cnf(c_0_150, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_32])).
% 12.47/12.64  cnf(c_0_151, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_114, c_0_145])).
% 12.47/12.64  cnf(c_0_152, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_153, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_100]), c_0_141]), c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_154, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_100]), c_0_141]), c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_155, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_156, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154])).
% 12.47/12.64  cnf(c_0_157, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_155, c_0_156])).
% 12.47/12.64  cnf(c_0_158, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_140, c_0_157])).
% 12.47/12.64  cnf(c_0_159, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_102, c_0_33])).
% 12.47/12.64  cnf(c_0_160, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_158, c_0_159])).
% 12.47/12.64  cnf(c_0_161, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_144]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_162, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_33])).
% 12.47/12.64  cnf(c_0_163, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_33])).
% 12.47/12.64  cnf(c_0_164, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_33])).
% 12.47/12.64  cnf(c_0_165, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_146, c_0_161])).
% 12.47/12.64  cnf(c_0_166, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_100]), c_0_142]), c_0_159]), c_0_163])).
% 12.47/12.64  cnf(c_0_167, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_100]), c_0_142]), c_0_159]), c_0_163])).
% 12.47/12.64  cnf(c_0_168, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_151, c_0_161])).
% 12.47/12.64  cnf(c_0_169, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_170, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_169]), c_0_163])).
% 12.47/12.64  cnf(c_0_171, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_158, c_0_170])).
% 12.47/12.64  cnf(c_0_172, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_144]), c_0_43])).
% 12.47/12.64  cnf(c_0_173, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_172])).
% 12.47/12.64  cnf(c_0_174, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_172])).
% 12.47/12.64  cnf(c_0_175, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_172])).
% 12.47/12.64  cnf(c_0_176, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_100]), c_0_145]), c_0_161]), c_0_174])).
% 12.47/12.64  cnf(c_0_177, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_100]), c_0_145]), c_0_161]), c_0_174])).
% 12.47/12.64  cnf(c_0_178, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_176]), c_0_177]), c_0_174])).
% 12.47/12.64  cnf(c_0_179, negated_conjecture, (v7_waybel_0(X1)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_118, c_0_145])).
% 12.47/12.64  cnf(c_0_180, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_119, c_0_145])).
% 12.47/12.64  cnf(c_0_181, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_120, c_0_145])).
% 12.47/12.64  cnf(c_0_182, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_178]), c_0_174])).
% 12.47/12.64  cnf(c_0_183, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v7_waybel_0(X1)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_184, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_185, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_186, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|~v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_128, c_0_182])).
% 12.47/12.64  cnf(c_0_187, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_183, c_0_156])).
% 12.47/12.64  cnf(c_0_188, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_184, c_0_156])).
% 12.47/12.64  cnf(c_0_189, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_153]), c_0_154])).
% 12.47/12.64  cnf(c_0_190, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_187]), c_0_188])).
% 12.47/12.64  cnf(c_0_191, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_32])).
% 12.47/12.64  cnf(c_0_192, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_190]), c_0_136])).
% 12.47/12.64  cnf(c_0_193, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_192]), c_0_156])).
% 12.47/12.64  cnf(c_0_194, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_140, c_0_193])).
% 12.47/12.64  cnf(c_0_195, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_194, c_0_159])).
% 12.47/12.64  cnf(c_0_196, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_144]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_197, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_146, c_0_196])).
% 12.47/12.64  cnf(c_0_198, negated_conjecture, (v7_waybel_0(X1)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_179, c_0_196])).
% 12.47/12.64  cnf(c_0_199, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_200, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_199]), c_0_163])).
% 12.47/12.64  cnf(c_0_201, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_194, c_0_200])).
% 12.47/12.64  cnf(c_0_202, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_144]), c_0_43])).
% 12.47/12.64  cnf(c_0_203, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_202])).
% 12.47/12.64  cnf(c_0_204, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_202])).
% 12.47/12.64  cnf(c_0_205, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_202])).
% 12.47/12.64  cnf(c_0_206, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_100]), c_0_145]), c_0_196]), c_0_204])).
% 12.47/12.64  cnf(c_0_207, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_100]), c_0_145]), c_0_196]), c_0_204])).
% 12.47/12.64  cnf(c_0_208, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_206]), c_0_207]), c_0_204])).
% 12.47/12.64  cnf(c_0_209, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_208]), c_0_204])).
% 12.47/12.64  cnf(c_0_210, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_180, c_0_196])).
% 12.47/12.64  cnf(c_0_211, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_181, c_0_196])).
% 12.47/12.64  cnf(c_0_212, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_186, c_0_209])).
% 12.47/12.64  cnf(c_0_213, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_210, c_0_199]), c_0_163])).
% 12.47/12.64  cnf(c_0_214, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_211, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_215, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_212, c_0_213])).
% 12.47/12.64  cnf(c_0_216, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_33])).
% 12.47/12.64  cnf(c_0_217, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_214, c_0_215]), c_0_136])).
% 12.47/12.64  cnf(c_0_218, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_216, c_0_217]), c_0_199])).
% 12.47/12.64  cnf(c_0_219, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_194, c_0_218])).
% 12.47/12.64  cnf(c_0_220, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_219, c_0_144]), c_0_43])).
% 12.47/12.64  cnf(c_0_221, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_220])).
% 12.47/12.64  cnf(c_0_222, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_220])).
% 12.47/12.64  cnf(c_0_223, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_220])).
% 12.47/12.64  cnf(c_0_224, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_221, c_0_100]), c_0_145]), c_0_196]), c_0_222])).
% 12.47/12.64  cnf(c_0_225, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_223, c_0_100]), c_0_145]), c_0_196]), c_0_222])).
% 12.47/12.64  cnf(c_0_226, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_224]), c_0_225]), c_0_222])).
% 12.47/12.64  cnf(c_0_227, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_210, c_0_226]), c_0_222])).
% 12.47/12.64  cnf(c_0_228, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_211, c_0_224]), c_0_225]), c_0_222])).
% 12.47/12.64  cnf(c_0_229, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_212, c_0_227])).
% 12.47/12.64  cnf(c_0_230, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_220])).
% 12.47/12.64  cnf(c_0_231, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_228, c_0_229]), c_0_136])).
% 12.47/12.64  cnf(c_0_232, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_44, c_0_139])).
% 12.47/12.64  cnf(c_0_233, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_139])).
% 12.47/12.64  cnf(c_0_234, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_230, c_0_231]), c_0_226])).
% 12.47/12.64  cnf(c_0_235, negated_conjecture, (v7_waybel_0(esk7_0)|v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_232, c_0_141]), c_0_142])).
% 12.47/12.64  cnf(c_0_236, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_233, c_0_141]), c_0_142])).
% 12.47/12.64  cnf(c_0_237, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~v7_waybel_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_55, c_0_234])).
% 12.47/12.64  cnf(c_0_238, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_235, c_0_144]), c_0_43]), c_0_101])).
% 12.47/12.64  cnf(c_0_239, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_236, c_0_144]), c_0_43]), c_0_101])).
% 12.47/12.64  cnf(c_0_240, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_237, c_0_238]), c_0_239])).
% 12.47/12.64  cnf(c_0_241, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_240])).
% 12.47/12.64  cnf(c_0_242, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_241]), c_0_68])])).
% 12.47/12.64  cnf(c_0_243, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_242]), c_0_24]), c_0_22])]), c_0_25]), c_0_145]), c_0_238]), c_0_239])).
% 12.47/12.64  cnf(c_0_244, negated_conjecture, (v1_compts_1(esk6_0)|v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_139]), c_0_32]), c_0_33]), c_0_43])).
% 12.47/12.64  cnf(c_0_245, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_77, c_0_139])).
% 12.47/12.64  cnf(c_0_246, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_244]), c_0_43]), c_0_101])).
% 12.47/12.64  cnf(c_0_247, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_245, c_0_141]), c_0_142])).
% 12.47/12.64  cnf(c_0_248, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_246]), c_0_101])).
% 12.47/12.64  cnf(c_0_249, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~v7_waybel_0(esk8_1(esk5_1(esk6_0)))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_85, c_0_234])).
% 12.47/12.64  cnf(c_0_250, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_81, c_0_240])).
% 12.47/12.64  cnf(c_0_251, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_247, c_0_246]), c_0_248])).
% 12.47/12.64  cnf(c_0_252, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_249, c_0_238]), c_0_250]), c_0_239])).
% 12.47/12.64  cnf(c_0_253, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_240])).
% 12.47/12.64  cnf(c_0_254, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_251, c_0_144]), c_0_43]), c_0_101])).
% 12.47/12.64  cnf(c_0_255, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_252, c_0_253]), c_0_254])).
% 12.47/12.64  cnf(c_0_256, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_255]), c_0_68])])).
% 12.47/12.64  cnf(c_0_257, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_256]), c_0_24]), c_0_22])]), c_0_25]), c_0_145]), c_0_238]), c_0_239])).
% 12.47/12.64  cnf(c_0_258, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_257, c_0_244]), c_0_43]), c_0_101])).
% 12.47/12.64  cnf(c_0_259, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_107, c_0_258])).
% 12.47/12.64  cnf(c_0_260, negated_conjecture, (v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_114, c_0_258])).
% 12.47/12.64  cnf(c_0_261, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_259, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_262, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_260, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_263, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_261, c_0_153]), c_0_154])).
% 12.47/12.64  cnf(c_0_264, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_262, c_0_263])).
% 12.47/12.64  cnf(c_0_265, negated_conjecture, (v7_waybel_0(X1)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_232, c_0_264])).
% 12.47/12.64  cnf(c_0_266, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v7_waybel_0(X1)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_265, c_0_159])).
% 12.47/12.64  cnf(c_0_267, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_266, c_0_144]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_268, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_259, c_0_267])).
% 12.47/12.64  cnf(c_0_269, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_260, c_0_267])).
% 12.47/12.64  cnf(c_0_270, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_268, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_271, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_269, c_0_270]), c_0_163])).
% 12.47/12.64  cnf(c_0_272, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v7_waybel_0(X1)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_265, c_0_271])).
% 12.47/12.64  cnf(c_0_273, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_272, c_0_144]), c_0_43])).
% 12.47/12.64  cnf(c_0_274, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_273])).
% 12.47/12.64  cnf(c_0_275, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_273])).
% 12.47/12.64  cnf(c_0_276, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_273])).
% 12.47/12.64  cnf(c_0_277, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_274, c_0_100]), c_0_258]), c_0_267]), c_0_275])).
% 12.47/12.64  cnf(c_0_278, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_276, c_0_100]), c_0_258]), c_0_267]), c_0_275])).
% 12.47/12.64  cnf(c_0_279, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_268, c_0_277]), c_0_278]), c_0_275])).
% 12.47/12.64  cnf(c_0_280, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_233, c_0_264])).
% 12.47/12.64  cnf(c_0_281, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_269, c_0_279]), c_0_275])).
% 12.47/12.64  cnf(c_0_282, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|l1_waybel_0(X1,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_280, c_0_159])).
% 12.47/12.64  cnf(c_0_283, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_237, c_0_281])).
% 12.47/12.64  cnf(c_0_284, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_282, c_0_144]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_285, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_283, c_0_284])).
% 12.47/12.64  cnf(c_0_286, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_285])).
% 12.47/12.64  cnf(c_0_287, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_286]), c_0_68])])).
% 12.47/12.64  cnf(c_0_288, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_287]), c_0_24]), c_0_22])]), c_0_25]), c_0_196]), c_0_267]), c_0_284])).
% 12.47/12.64  cnf(c_0_289, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_245, c_0_264])).
% 12.47/12.64  cnf(c_0_290, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_288, c_0_244]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_291, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_289, c_0_159])).
% 12.47/12.64  cnf(c_0_292, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_290]), c_0_102])).
% 12.47/12.64  cnf(c_0_293, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_249, c_0_281])).
% 12.47/12.64  cnf(c_0_294, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_291, c_0_290]), c_0_292])).
% 12.47/12.64  cnf(c_0_295, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_293, c_0_284])).
% 12.47/12.64  cnf(c_0_296, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_294, c_0_144]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_297, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_295, c_0_290]), c_0_296])).
% 12.47/12.64  cnf(c_0_298, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_285])).
% 12.47/12.64  cnf(c_0_299, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_297, c_0_298])).
% 12.47/12.64  cnf(c_0_300, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_299]), c_0_68])])).
% 12.47/12.64  cnf(c_0_301, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_300]), c_0_24]), c_0_22])]), c_0_25]), c_0_196]), c_0_267]), c_0_284])).
% 12.47/12.64  cnf(c_0_302, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_301, c_0_244]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_303, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_259, c_0_302])).
% 12.47/12.64  cnf(c_0_304, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_260, c_0_302])).
% 12.47/12.64  cnf(c_0_305, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_303, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_306, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_304, c_0_305]), c_0_163])).
% 12.47/12.64  cnf(c_0_307, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_280, c_0_306])).
% 12.47/12.64  cnf(c_0_308, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_307, c_0_144]), c_0_43])).
% 12.47/12.64  cnf(c_0_309, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_308])).
% 12.47/12.64  cnf(c_0_310, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_308])).
% 12.47/12.64  cnf(c_0_311, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_308])).
% 12.47/12.64  cnf(c_0_312, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_309, c_0_100]), c_0_258]), c_0_302]), c_0_310])).
% 12.47/12.64  cnf(c_0_313, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_311, c_0_100]), c_0_258]), c_0_302]), c_0_310])).
% 12.47/12.64  cnf(c_0_314, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_303, c_0_312]), c_0_313]), c_0_310])).
% 12.47/12.64  cnf(c_0_315, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_304, c_0_314]), c_0_310])).
% 12.47/12.64  cnf(c_0_316, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_283, c_0_315])).
% 12.47/12.64  cnf(c_0_317, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_316])).
% 12.47/12.64  cnf(c_0_318, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_317]), c_0_68])])).
% 12.47/12.64  cnf(c_0_319, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_318]), c_0_24]), c_0_22])]), c_0_25]), c_0_234]), c_0_281]), c_0_315])).
% 12.47/12.64  cnf(c_0_320, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_319, c_0_244]), c_0_43])).
% 12.47/12.64  cnf(c_0_321, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_320])).
% 12.47/12.64  cnf(c_0_322, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_320])).
% 12.47/12.64  cnf(c_0_323, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_289, c_0_306])).
% 12.47/12.64  cnf(c_0_324, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_321, c_0_100]), c_0_258]), c_0_302]), c_0_322])).
% 12.47/12.64  cnf(c_0_325, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_81, c_0_316])).
% 12.47/12.64  cnf(c_0_326, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_323, c_0_324])).
% 12.47/12.64  cnf(c_0_327, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_324]), c_0_43])).
% 12.47/12.64  cnf(c_0_328, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_293, c_0_315]), c_0_325])).
% 12.47/12.64  cnf(c_0_329, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_316])).
% 12.47/12.64  cnf(c_0_330, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_326, c_0_144]), c_0_43]), c_0_327])).
% 12.47/12.64  cnf(c_0_331, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_328, c_0_329])).
% 12.47/12.64  cnf(c_0_332, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_330, c_0_331]), c_0_43])).
% 12.47/12.64  cnf(c_0_333, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_332]), c_0_68])])).
% 12.47/12.64  cnf(c_0_334, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_333]), c_0_24]), c_0_22])]), c_0_25]), c_0_220]), c_0_273]), c_0_308]), c_0_244])).
% 12.47/12.64  cnf(c_0_335, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_334])).
% 12.47/12.64  cnf(c_0_336, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_334])).
% 12.47/12.64  cnf(c_0_337, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_335, c_0_100]), c_0_258]), c_0_302]), c_0_336])).
% 12.47/12.64  cnf(c_0_338, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_320])).
% 12.47/12.64  cnf(c_0_339, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_303, c_0_337])).
% 12.47/12.64  cnf(c_0_340, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_338, c_0_100]), c_0_258]), c_0_302]), c_0_322])).
% 12.47/12.64  cnf(c_0_341, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_339, c_0_340]), c_0_322])).
% 12.47/12.64  cnf(c_0_342, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_304, c_0_341]), c_0_322])).
% 12.47/12.64  cnf(c_0_343, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_323, c_0_342])).
% 12.47/12.64  cnf(c_0_344, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_342]), c_0_43])).
% 12.47/12.64  cnf(c_0_345, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_343, c_0_144]), c_0_43]), c_0_344])).
% 12.47/12.64  cnf(c_0_346, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_345, c_0_331]), c_0_43])).
% 12.47/12.64  cnf(c_0_347, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_346]), c_0_68])])).
% 12.47/12.64  cnf(c_0_348, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_347]), c_0_24]), c_0_22])]), c_0_25]), c_0_220]), c_0_273]), c_0_308]), c_0_244])).
% 12.47/12.64  cnf(c_0_349, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_348])).
% 12.47/12.64  cnf(c_0_350, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_348])).
% 12.47/12.64  cnf(c_0_351, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_349, c_0_100]), c_0_258]), c_0_302]), c_0_350])).
% 12.47/12.64  cnf(c_0_352, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_339, c_0_351]), c_0_350])).
% 12.47/12.64  cnf(c_0_353, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_118, c_0_258])).
% 12.47/12.64  cnf(c_0_354, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_119, c_0_258])).
% 12.47/12.64  cnf(c_0_355, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_120, c_0_258])).
% 12.47/12.64  cnf(c_0_356, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_304, c_0_352]), c_0_350])).
% 12.47/12.64  cnf(c_0_357, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_353, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_358, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_354, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_359, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_355, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_360, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|~v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_128, c_0_356])).
% 12.47/12.64  cnf(c_0_361, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_357, c_0_263])).
% 12.47/12.64  cnf(c_0_362, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_358, c_0_263])).
% 12.47/12.64  cnf(c_0_363, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_359, c_0_153]), c_0_154])).
% 12.47/12.64  cnf(c_0_364, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_360, c_0_361]), c_0_362])).
% 12.47/12.64  cnf(c_0_365, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_363, c_0_364]), c_0_136])).
% 12.47/12.64  cnf(c_0_366, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_365]), c_0_263])).
% 12.47/12.64  cnf(c_0_367, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_232, c_0_366])).
% 12.47/12.64  cnf(c_0_368, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_367, c_0_159])).
% 12.47/12.64  cnf(c_0_369, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_368, c_0_144]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_370, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_259, c_0_369])).
% 12.47/12.64  cnf(c_0_371, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_353, c_0_369])).
% 12.47/12.64  cnf(c_0_372, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_370, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_373, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_371, c_0_372]), c_0_163])).
% 12.47/12.64  cnf(c_0_374, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_367, c_0_373])).
% 12.47/12.64  cnf(c_0_375, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_374, c_0_144]), c_0_43])).
% 12.47/12.64  cnf(c_0_376, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_375])).
% 12.47/12.64  cnf(c_0_377, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_375])).
% 12.47/12.64  cnf(c_0_378, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_375])).
% 12.47/12.64  cnf(c_0_379, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_376, c_0_100]), c_0_258]), c_0_369]), c_0_377])).
% 12.47/12.64  cnf(c_0_380, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_378, c_0_100]), c_0_258]), c_0_369]), c_0_377])).
% 12.47/12.64  cnf(c_0_381, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_370, c_0_379]), c_0_380]), c_0_377])).
% 12.47/12.64  cnf(c_0_382, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_371, c_0_381]), c_0_377])).
% 12.47/12.64  cnf(c_0_383, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_354, c_0_369])).
% 12.47/12.64  cnf(c_0_384, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_355, c_0_369])).
% 12.47/12.64  cnf(c_0_385, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_360, c_0_382])).
% 12.47/12.64  cnf(c_0_386, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_383, c_0_372]), c_0_163])).
% 12.47/12.64  cnf(c_0_387, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_384, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_388, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_385, c_0_386])).
% 12.47/12.64  cnf(c_0_389, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_387, c_0_388]), c_0_136])).
% 12.47/12.64  cnf(c_0_390, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_216, c_0_389]), c_0_372])).
% 12.47/12.64  cnf(c_0_391, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_367, c_0_390])).
% 12.47/12.64  cnf(c_0_392, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_391, c_0_144]), c_0_43])).
% 12.47/12.64  cnf(c_0_393, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_392])).
% 12.47/12.64  cnf(c_0_394, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_392])).
% 12.47/12.64  cnf(c_0_395, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_392])).
% 12.47/12.64  cnf(c_0_396, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_393, c_0_100]), c_0_258]), c_0_369]), c_0_394])).
% 12.47/12.64  cnf(c_0_397, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_395, c_0_100]), c_0_258]), c_0_369]), c_0_394])).
% 12.47/12.64  cnf(c_0_398, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_370, c_0_396]), c_0_397]), c_0_394])).
% 12.47/12.64  cnf(c_0_399, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_383, c_0_398]), c_0_394])).
% 12.47/12.64  cnf(c_0_400, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_384, c_0_396]), c_0_397]), c_0_394])).
% 12.47/12.64  cnf(c_0_401, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_385, c_0_399])).
% 12.47/12.64  cnf(c_0_402, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_392])).
% 12.47/12.64  cnf(c_0_403, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_400, c_0_401]), c_0_136])).
% 12.47/12.64  cnf(c_0_404, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_233, c_0_366])).
% 12.47/12.64  cnf(c_0_405, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_402, c_0_403]), c_0_398])).
% 12.47/12.64  cnf(c_0_406, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_404, c_0_159])).
% 12.47/12.64  cnf(c_0_407, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_237, c_0_405])).
% 12.47/12.64  cnf(c_0_408, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_406, c_0_144]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_409, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_407, c_0_408])).
% 12.47/12.64  cnf(c_0_410, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_409])).
% 12.47/12.64  cnf(c_0_411, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_410]), c_0_68])])).
% 12.47/12.64  cnf(c_0_412, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_411]), c_0_24]), c_0_22])]), c_0_25]), c_0_196]), c_0_369]), c_0_408])).
% 12.47/12.64  cnf(c_0_413, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_245, c_0_366])).
% 12.47/12.64  cnf(c_0_414, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_412, c_0_244]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_415, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_413, c_0_159])).
% 12.47/12.64  cnf(c_0_416, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_414]), c_0_102])).
% 12.47/12.64  cnf(c_0_417, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_249, c_0_405])).
% 12.47/12.64  cnf(c_0_418, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_415, c_0_414]), c_0_416])).
% 12.47/12.64  cnf(c_0_419, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_417, c_0_408])).
% 12.47/12.64  cnf(c_0_420, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_418, c_0_144]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_421, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_419, c_0_414]), c_0_420])).
% 12.47/12.64  cnf(c_0_422, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_409]), c_0_421])).
% 12.47/12.64  cnf(c_0_423, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_422]), c_0_68])])).
% 12.47/12.64  cnf(c_0_424, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_423]), c_0_24]), c_0_22])]), c_0_25]), c_0_196]), c_0_369]), c_0_408])).
% 12.47/12.64  cnf(c_0_425, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_424, c_0_244]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_426, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_259, c_0_425])).
% 12.47/12.64  cnf(c_0_427, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_353, c_0_425])).
% 12.47/12.64  cnf(c_0_428, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_426, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_429, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_427, c_0_428]), c_0_163])).
% 12.47/12.64  cnf(c_0_430, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_404, c_0_429])).
% 12.47/12.64  cnf(c_0_431, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_430, c_0_144]), c_0_43])).
% 12.47/12.64  cnf(c_0_432, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_431])).
% 12.47/12.64  cnf(c_0_433, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_431])).
% 12.47/12.64  cnf(c_0_434, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_431])).
% 12.47/12.64  cnf(c_0_435, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_432, c_0_100]), c_0_258]), c_0_425]), c_0_433])).
% 12.47/12.64  cnf(c_0_436, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_434, c_0_100]), c_0_258]), c_0_425]), c_0_433])).
% 12.47/12.64  cnf(c_0_437, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_426, c_0_435]), c_0_436]), c_0_433])).
% 12.47/12.64  cnf(c_0_438, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_427, c_0_437]), c_0_433])).
% 12.47/12.64  cnf(c_0_439, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_407, c_0_438])).
% 12.47/12.64  cnf(c_0_440, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_439])).
% 12.47/12.64  cnf(c_0_441, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_440]), c_0_68])])).
% 12.47/12.64  cnf(c_0_442, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_441]), c_0_24]), c_0_22])]), c_0_25]), c_0_234]), c_0_405]), c_0_438])).
% 12.47/12.64  cnf(c_0_443, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_442, c_0_244]), c_0_43])).
% 12.47/12.64  cnf(c_0_444, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_443])).
% 12.47/12.64  cnf(c_0_445, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_443])).
% 12.47/12.64  cnf(c_0_446, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_413, c_0_429])).
% 12.47/12.64  cnf(c_0_447, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_444, c_0_100]), c_0_258]), c_0_425]), c_0_445])).
% 12.47/12.64  cnf(c_0_448, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_417, c_0_438])).
% 12.47/12.64  cnf(c_0_449, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_446, c_0_447])).
% 12.47/12.64  cnf(c_0_450, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_447]), c_0_43])).
% 12.47/12.64  cnf(c_0_451, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_448, c_0_447])).
% 12.47/12.64  cnf(c_0_452, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_439])).
% 12.47/12.64  cnf(c_0_453, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_449, c_0_144]), c_0_43]), c_0_450])).
% 12.47/12.64  cnf(c_0_454, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_451, c_0_452])).
% 12.47/12.64  cnf(c_0_455, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_453, c_0_454]), c_0_43])).
% 12.47/12.64  cnf(c_0_456, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_455]), c_0_68])])).
% 12.47/12.64  cnf(c_0_457, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_456]), c_0_24]), c_0_22])]), c_0_25]), c_0_220]), c_0_392]), c_0_431]), c_0_244])).
% 12.47/12.64  cnf(c_0_458, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_457])).
% 12.47/12.64  cnf(c_0_459, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_457])).
% 12.47/12.64  cnf(c_0_460, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_458, c_0_100]), c_0_258]), c_0_425]), c_0_459])).
% 12.47/12.64  cnf(c_0_461, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_443])).
% 12.47/12.64  cnf(c_0_462, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_426, c_0_460]), c_0_427])).
% 12.47/12.64  cnf(c_0_463, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_461, c_0_100]), c_0_258]), c_0_425]), c_0_445])).
% 12.47/12.64  cnf(c_0_464, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_462, c_0_463]), c_0_445])).
% 12.47/12.64  cnf(c_0_465, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_446, c_0_464])).
% 12.47/12.64  cnf(c_0_466, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_464]), c_0_43])).
% 12.47/12.64  cnf(c_0_467, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_448, c_0_464])).
% 12.47/12.64  cnf(c_0_468, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_465, c_0_144]), c_0_43]), c_0_466])).
% 12.47/12.64  cnf(c_0_469, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_467, c_0_452])).
% 12.47/12.64  cnf(c_0_470, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_468, c_0_469]), c_0_43])).
% 12.47/12.64  cnf(c_0_471, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_470]), c_0_68])])).
% 12.47/12.64  cnf(c_0_472, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_471]), c_0_24]), c_0_22])]), c_0_25]), c_0_220]), c_0_392]), c_0_431]), c_0_244])).
% 12.47/12.64  cnf(c_0_473, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_472])).
% 12.47/12.64  cnf(c_0_474, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_472])).
% 12.47/12.64  cnf(c_0_475, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_473, c_0_100]), c_0_258]), c_0_425]), c_0_474])).
% 12.47/12.64  cnf(c_0_476, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_462, c_0_475]), c_0_474])).
% 12.47/12.64  cnf(c_0_477, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_354, c_0_425])).
% 12.47/12.64  cnf(c_0_478, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_355, c_0_425])).
% 12.47/12.64  cnf(c_0_479, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_360, c_0_476])).
% 12.47/12.64  cnf(c_0_480, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_477, c_0_428]), c_0_163])).
% 12.47/12.64  cnf(c_0_481, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_478, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_482, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_479, c_0_480])).
% 12.47/12.64  cnf(c_0_483, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_481, c_0_482]), c_0_136])).
% 12.47/12.64  cnf(c_0_484, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_216, c_0_483]), c_0_428])).
% 12.47/12.64  cnf(c_0_485, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_404, c_0_484])).
% 12.47/12.64  cnf(c_0_486, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_485, c_0_144]), c_0_43])).
% 12.47/12.64  cnf(c_0_487, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_486])).
% 12.47/12.64  cnf(c_0_488, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_486])).
% 12.47/12.64  cnf(c_0_489, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_486])).
% 12.47/12.64  cnf(c_0_490, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_487, c_0_100]), c_0_258]), c_0_425]), c_0_488])).
% 12.47/12.64  cnf(c_0_491, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_489, c_0_100]), c_0_258]), c_0_425]), c_0_488])).
% 12.47/12.64  cnf(c_0_492, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_426, c_0_490]), c_0_491]), c_0_488])).
% 12.47/12.64  cnf(c_0_493, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_477, c_0_492]), c_0_488])).
% 12.47/12.64  cnf(c_0_494, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_478, c_0_490]), c_0_491]), c_0_488])).
% 12.47/12.64  cnf(c_0_495, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_479, c_0_493])).
% 12.47/12.64  cnf(c_0_496, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_486])).
% 12.47/12.64  cnf(c_0_497, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_494, c_0_495]), c_0_136])).
% 12.47/12.64  cnf(c_0_498, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_496, c_0_497]), c_0_492])).
% 12.47/12.64  cnf(c_0_499, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_407, c_0_498])).
% 12.47/12.64  cnf(c_0_500, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_499])).
% 12.47/12.64  cnf(c_0_501, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_500]), c_0_68])])).
% 12.47/12.64  cnf(c_0_502, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_501]), c_0_24]), c_0_22])]), c_0_25]), c_0_234]), c_0_405]), c_0_498])).
% 12.47/12.64  cnf(c_0_503, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_502, c_0_244]), c_0_43])).
% 12.47/12.64  cnf(c_0_504, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_503])).
% 12.47/12.64  cnf(c_0_505, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_503])).
% 12.47/12.64  cnf(c_0_506, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_413, c_0_484])).
% 12.47/12.64  cnf(c_0_507, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_504, c_0_100]), c_0_258]), c_0_425]), c_0_505])).
% 12.47/12.64  cnf(c_0_508, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_417, c_0_498])).
% 12.47/12.64  cnf(c_0_509, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_506, c_0_507])).
% 12.47/12.64  cnf(c_0_510, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_507]), c_0_43])).
% 12.47/12.64  cnf(c_0_511, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_508, c_0_507])).
% 12.47/12.64  cnf(c_0_512, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_499])).
% 12.47/12.64  cnf(c_0_513, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_509, c_0_144]), c_0_43]), c_0_510])).
% 12.47/12.64  cnf(c_0_514, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_511, c_0_512])).
% 12.47/12.64  cnf(c_0_515, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_513, c_0_514]), c_0_43])).
% 12.47/12.64  cnf(c_0_516, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_515]), c_0_68])])).
% 12.47/12.64  cnf(c_0_517, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_516]), c_0_24]), c_0_22])]), c_0_25]), c_0_220]), c_0_392]), c_0_486]), c_0_244])).
% 12.47/12.64  cnf(c_0_518, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_517])).
% 12.47/12.64  cnf(c_0_519, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_517])).
% 12.47/12.64  cnf(c_0_520, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_518, c_0_100]), c_0_258]), c_0_425]), c_0_519])).
% 12.47/12.64  cnf(c_0_521, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_503])).
% 12.47/12.64  cnf(c_0_522, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_426, c_0_520])).
% 12.47/12.64  cnf(c_0_523, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_521, c_0_100]), c_0_258]), c_0_425]), c_0_505])).
% 12.47/12.64  cnf(c_0_524, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_522, c_0_523]), c_0_505])).
% 12.47/12.64  cnf(c_0_525, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_477, c_0_524]), c_0_505])).
% 12.47/12.64  cnf(c_0_526, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_506, c_0_525])).
% 12.47/12.64  cnf(c_0_527, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_525]), c_0_43])).
% 12.47/12.64  cnf(c_0_528, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_508, c_0_525])).
% 12.47/12.64  cnf(c_0_529, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_526, c_0_144]), c_0_43]), c_0_527])).
% 12.47/12.64  cnf(c_0_530, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_528, c_0_512])).
% 12.47/12.64  cnf(c_0_531, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_529, c_0_530]), c_0_43])).
% 12.47/12.64  cnf(c_0_532, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_531]), c_0_68])])).
% 12.47/12.64  cnf(c_0_533, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_532]), c_0_24]), c_0_22])]), c_0_25]), c_0_220]), c_0_392]), c_0_486]), c_0_244])).
% 12.47/12.64  cnf(c_0_534, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_533])).
% 12.47/12.64  cnf(c_0_535, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_533])).
% 12.47/12.64  cnf(c_0_536, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_30, c_0_220])).
% 12.47/12.64  cnf(c_0_537, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_534, c_0_100]), c_0_258]), c_0_425]), c_0_535])).
% 12.47/12.64  cnf(c_0_538, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~v7_waybel_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_55, c_0_536])).
% 12.47/12.64  cnf(c_0_539, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_30, c_0_392])).
% 12.47/12.64  cnf(c_0_540, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_522, c_0_537]), c_0_535])).
% 12.47/12.64  cnf(c_0_541, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_538, c_0_539])).
% 12.47/12.64  cnf(c_0_542, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_30, c_0_486])).
% 12.47/12.64  cnf(c_0_543, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))|~r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_478, c_0_520])).
% 12.47/12.64  cnf(c_0_544, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_477, c_0_540]), c_0_535])).
% 12.47/12.64  cnf(c_0_545, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_541, c_0_542])).
% 12.47/12.64  cnf(c_0_546, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_543, c_0_523]), c_0_505])).
% 12.47/12.64  cnf(c_0_547, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_479, c_0_544])).
% 12.47/12.64  cnf(c_0_548, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~v7_waybel_0(esk8_1(esk5_1(esk6_0)))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_85, c_0_536])).
% 12.47/12.64  cnf(c_0_549, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_545])).
% 12.47/12.64  cnf(c_0_550, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_503])).
% 12.47/12.64  cnf(c_0_551, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_546, c_0_547]), c_0_136])).
% 12.47/12.64  cnf(c_0_552, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_548, c_0_539])).
% 12.47/12.64  cnf(c_0_553, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_549]), c_0_68])])).
% 12.47/12.64  cnf(c_0_554, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_550, c_0_551]), c_0_524])).
% 12.47/12.64  cnf(c_0_555, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_552, c_0_542])).
% 12.47/12.64  cnf(c_0_556, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_553]), c_0_24]), c_0_22])]), c_0_25]), c_0_536]), c_0_539]), c_0_542]), c_0_74])).
% 12.47/12.64  cnf(c_0_557, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_506, c_0_554])).
% 12.47/12.64  cnf(c_0_558, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_554]), c_0_43])).
% 12.47/12.64  cnf(c_0_559, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_508, c_0_554])).
% 12.47/12.64  cnf(c_0_560, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_555, c_0_556])).
% 12.47/12.64  cnf(c_0_561, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_545])).
% 12.47/12.64  cnf(c_0_562, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_557, c_0_144]), c_0_43]), c_0_558])).
% 12.47/12.64  cnf(c_0_563, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_559, c_0_512])).
% 12.47/12.64  cnf(c_0_564, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_560, c_0_561])).
% 12.47/12.64  cnf(c_0_565, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_562, c_0_563]), c_0_43])).
% 12.47/12.64  cnf(c_0_566, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_562, c_0_564]), c_0_30])).
% 12.47/12.64  cnf(c_0_567, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_565]), c_0_68])])).
% 12.47/12.64  cnf(c_0_568, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_566]), c_0_68])])).
% 12.47/12.64  cnf(c_0_569, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_567]), c_0_24]), c_0_22])]), c_0_25]), c_0_220]), c_0_392]), c_0_486]), c_0_244])).
% 12.47/12.64  cnf(c_0_570, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_568]), c_0_24]), c_0_22])]), c_0_25]), c_0_536]), c_0_539]), c_0_542]), c_0_74])).
% 12.47/12.64  cnf(c_0_571, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_569])).
% 12.47/12.64  cnf(c_0_572, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_569])).
% 12.47/12.64  cnf(c_0_573, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_570]), c_0_258]), c_0_425]), c_0_571])).
% 12.47/12.64  cnf(c_0_574, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_518, c_0_570]), c_0_258]), c_0_425]), c_0_519])).
% 12.47/12.64  cnf(c_0_575, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_572, c_0_570]), c_0_258]), c_0_425]), c_0_571])).
% 12.47/12.64  cnf(c_0_576, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_573, c_0_574]), c_0_575])).
% 12.47/12.64  cnf(c_0_577, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_570]), c_0_258]), c_0_425]), c_0_571])).
% 12.47/12.64  cnf(c_0_578, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 12.47/12.64  cnf(c_0_579, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_569])).
% 12.47/12.64  cnf(c_0_580, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_576, c_0_547]), c_0_136])).
% 12.47/12.64  cnf(c_0_581, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_577, c_0_574]), c_0_575])).
% 12.47/12.64  cnf(c_0_582, negated_conjecture, (v2_struct_0(X1)|~m2_yellow_6(X2,esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_struct_0(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_578, c_0_29]), c_0_25])).
% 12.47/12.64  cnf(c_0_583, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_579, c_0_580]), c_0_581])).
% 12.47/12.64  cnf(c_0_584, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(X1)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_582, c_0_583])).
% 12.47/12.64  cnf(c_0_585, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_584, c_0_100])).
% 12.47/12.64  cnf(c_0_586, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_585, c_0_108]), c_0_109]), c_0_123]), c_0_110])).
% 12.47/12.64  cnf(c_0_587, negated_conjecture, (v4_orders_2(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_586])).
% 12.47/12.64  cnf(c_0_588, negated_conjecture, (v7_waybel_0(esk7_0)|v4_orders_2(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_587, c_0_141]), c_0_142])).
% 12.47/12.64  cnf(c_0_589, negated_conjecture, (v1_compts_1(esk6_0)|m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_586]), c_0_32]), c_0_33]), c_0_43])).
% 12.47/12.64  cnf(c_0_590, negated_conjecture, (v7_waybel_0(esk7_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_588, c_0_589]), c_0_43]), c_0_101])).
% 12.47/12.64  cnf(c_0_591, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_107, c_0_590])).
% 12.47/12.64  cnf(c_0_592, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_585, c_0_590])).
% 12.47/12.64  cnf(c_0_593, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_591, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_594, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_592, c_0_147]), c_0_148])).
% 12.47/12.64  cnf(c_0_595, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_593, c_0_153]), c_0_154]), c_0_594])).
% 12.47/12.64  cnf(c_0_596, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_587, c_0_595])).
% 12.47/12.64  cnf(c_0_597, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_596, c_0_159])).
% 12.47/12.64  cnf(c_0_598, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_597, c_0_589]), c_0_43]), c_0_102])).
% 12.47/12.64  cnf(c_0_599, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_591, c_0_598])).
% 12.47/12.64  cnf(c_0_600, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_592, c_0_598])).
% 12.47/12.64  cnf(c_0_601, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_599, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.64  cnf(c_0_602, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_600, c_0_601]), c_0_163])).
% 12.47/12.64  cnf(c_0_603, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_596, c_0_602])).
% 12.47/12.64  cnf(c_0_604, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_603, c_0_589]), c_0_43])).
% 12.47/12.64  cnf(c_0_605, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_604])).
% 12.47/12.64  cnf(c_0_606, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_604])).
% 12.47/12.64  cnf(c_0_607, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_604])).
% 12.47/12.64  cnf(c_0_608, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_605, c_0_100]), c_0_590]), c_0_598]), c_0_606])).
% 12.47/12.64  cnf(c_0_609, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_607, c_0_100]), c_0_590]), c_0_598]), c_0_606])).
% 12.47/12.64  cnf(c_0_610, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_599, c_0_608]), c_0_609]), c_0_606])).
% 12.47/12.64  cnf(c_0_611, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_44, c_0_586])).
% 12.47/12.64  cnf(c_0_612, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_586])).
% 12.47/12.64  cnf(c_0_613, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_600, c_0_610]), c_0_606])).
% 12.47/12.64  cnf(c_0_614, negated_conjecture, (v7_waybel_0(esk7_0)|v7_waybel_0(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_611, c_0_141]), c_0_142])).
% 12.47/12.64  cnf(c_0_615, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_612, c_0_141]), c_0_142])).
% 12.47/12.64  cnf(c_0_616, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~v7_waybel_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_55, c_0_613])).
% 12.47/12.64  cnf(c_0_617, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_614, c_0_589]), c_0_43]), c_0_101])).
% 12.47/12.64  cnf(c_0_618, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_615, c_0_589]), c_0_43]), c_0_101])).
% 12.47/12.64  cnf(c_0_619, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_616, c_0_617]), c_0_618])).
% 12.47/12.64  cnf(c_0_620, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_619])).
% 12.47/12.64  cnf(c_0_621, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_620]), c_0_68])])).
% 12.47/12.65  cnf(c_0_622, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_621]), c_0_24]), c_0_22])]), c_0_25]), c_0_590]), c_0_617]), c_0_618])).
% 12.47/12.65  cnf(c_0_623, negated_conjecture, (v1_compts_1(esk6_0)|v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_586]), c_0_32]), c_0_33]), c_0_43])).
% 12.47/12.65  cnf(c_0_624, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_77, c_0_586])).
% 12.47/12.65  cnf(c_0_625, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_622, c_0_623]), c_0_43]), c_0_101])).
% 12.47/12.65  cnf(c_0_626, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_624, c_0_141]), c_0_142])).
% 12.47/12.65  cnf(c_0_627, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_625]), c_0_101])).
% 12.47/12.65  cnf(c_0_628, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~v7_waybel_0(esk8_1(esk5_1(esk6_0)))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_85, c_0_613])).
% 12.47/12.65  cnf(c_0_629, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_81, c_0_619])).
% 12.47/12.65  cnf(c_0_630, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_626, c_0_625]), c_0_627])).
% 12.47/12.65  cnf(c_0_631, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_628, c_0_617]), c_0_629]), c_0_618])).
% 12.47/12.65  cnf(c_0_632, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_619])).
% 12.47/12.65  cnf(c_0_633, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_630, c_0_589]), c_0_43]), c_0_101])).
% 12.47/12.65  cnf(c_0_634, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_631, c_0_632]), c_0_633])).
% 12.47/12.65  cnf(c_0_635, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_634]), c_0_68])])).
% 12.47/12.65  cnf(c_0_636, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_635]), c_0_24]), c_0_22])]), c_0_25]), c_0_590]), c_0_617]), c_0_618])).
% 12.47/12.65  cnf(c_0_637, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_636, c_0_623]), c_0_43]), c_0_101])).
% 12.47/12.65  cnf(c_0_638, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_107, c_0_637])).
% 12.47/12.65  cnf(c_0_639, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_585, c_0_637])).
% 12.47/12.65  cnf(c_0_640, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_638, c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_641, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_639, c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_642, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_640, c_0_153]), c_0_154]), c_0_641])).
% 12.47/12.65  cnf(c_0_643, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_611, c_0_642])).
% 12.47/12.65  cnf(c_0_644, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v7_waybel_0(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_643, c_0_159])).
% 12.47/12.65  cnf(c_0_645, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_644, c_0_589]), c_0_43]), c_0_102])).
% 12.47/12.65  cnf(c_0_646, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_638, c_0_645])).
% 12.47/12.65  cnf(c_0_647, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_639, c_0_645])).
% 12.47/12.65  cnf(c_0_648, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_646, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.65  cnf(c_0_649, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_647, c_0_648]), c_0_163])).
% 12.47/12.65  cnf(c_0_650, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v7_waybel_0(X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_643, c_0_649])).
% 12.47/12.65  cnf(c_0_651, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_650, c_0_589]), c_0_43])).
% 12.47/12.65  cnf(c_0_652, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_651])).
% 12.47/12.65  cnf(c_0_653, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_651])).
% 12.47/12.65  cnf(c_0_654, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_651])).
% 12.47/12.65  cnf(c_0_655, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_652, c_0_100]), c_0_637]), c_0_645]), c_0_653])).
% 12.47/12.65  cnf(c_0_656, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_654, c_0_100]), c_0_637]), c_0_645]), c_0_653])).
% 12.47/12.65  cnf(c_0_657, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_646, c_0_655]), c_0_656]), c_0_653])).
% 12.47/12.65  cnf(c_0_658, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_612, c_0_642])).
% 12.47/12.65  cnf(c_0_659, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_647, c_0_657]), c_0_653])).
% 12.47/12.65  cnf(c_0_660, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|l1_waybel_0(X1,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_658, c_0_159])).
% 12.47/12.65  cnf(c_0_661, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_616, c_0_659])).
% 12.47/12.65  cnf(c_0_662, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_660, c_0_589]), c_0_43]), c_0_102])).
% 12.47/12.65  cnf(c_0_663, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_661, c_0_662])).
% 12.47/12.65  cnf(c_0_664, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_663])).
% 12.47/12.65  cnf(c_0_665, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_664]), c_0_68])])).
% 12.47/12.65  cnf(c_0_666, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_665]), c_0_24]), c_0_22])]), c_0_25]), c_0_598]), c_0_645]), c_0_662])).
% 12.47/12.65  cnf(c_0_667, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_624, c_0_642])).
% 12.47/12.65  cnf(c_0_668, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_666, c_0_623]), c_0_43]), c_0_102])).
% 12.47/12.65  cnf(c_0_669, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_667, c_0_159])).
% 12.47/12.65  cnf(c_0_670, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_668]), c_0_102])).
% 12.47/12.65  cnf(c_0_671, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_628, c_0_659])).
% 12.47/12.65  cnf(c_0_672, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_669, c_0_668]), c_0_670])).
% 12.47/12.65  cnf(c_0_673, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_671, c_0_662])).
% 12.47/12.65  cnf(c_0_674, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_672, c_0_589]), c_0_43]), c_0_102])).
% 12.47/12.65  cnf(c_0_675, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_673, c_0_668]), c_0_674])).
% 12.47/12.65  cnf(c_0_676, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_663])).
% 12.47/12.65  cnf(c_0_677, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_675, c_0_676])).
% 12.47/12.65  cnf(c_0_678, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_677]), c_0_68])])).
% 12.47/12.65  cnf(c_0_679, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_678]), c_0_24]), c_0_22])]), c_0_25]), c_0_598]), c_0_645]), c_0_662])).
% 12.47/12.65  cnf(c_0_680, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_679, c_0_623]), c_0_43]), c_0_102])).
% 12.47/12.65  cnf(c_0_681, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_638, c_0_680])).
% 12.47/12.65  cnf(c_0_682, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_639, c_0_680])).
% 12.47/12.65  cnf(c_0_683, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_681, c_0_166]), c_0_167]), c_0_163])).
% 12.47/12.65  cnf(c_0_684, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_682, c_0_683]), c_0_163])).
% 12.47/12.65  cnf(c_0_685, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_658, c_0_684])).
% 12.47/12.65  cnf(c_0_686, negated_conjecture, (v1_compts_1(esk6_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_685, c_0_589]), c_0_43])).
% 12.47/12.65  cnf(c_0_687, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_686])).
% 12.47/12.65  cnf(c_0_688, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_686])).
% 12.47/12.65  cnf(c_0_689, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_686])).
% 12.47/12.65  cnf(c_0_690, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_687, c_0_100]), c_0_637]), c_0_680]), c_0_688])).
% 12.47/12.65  cnf(c_0_691, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_689, c_0_100]), c_0_637]), c_0_680]), c_0_688])).
% 12.47/12.65  cnf(c_0_692, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_681, c_0_690]), c_0_691]), c_0_688])).
% 12.47/12.65  cnf(c_0_693, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_682, c_0_692]), c_0_688])).
% 12.47/12.65  cnf(c_0_694, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_661, c_0_693])).
% 12.47/12.65  cnf(c_0_695, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_694])).
% 12.47/12.65  cnf(c_0_696, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_695]), c_0_68])])).
% 12.47/12.65  cnf(c_0_697, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v3_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_696]), c_0_24]), c_0_22])]), c_0_25]), c_0_613]), c_0_659]), c_0_693])).
% 12.47/12.65  cnf(c_0_698, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_697, c_0_623]), c_0_43])).
% 12.47/12.65  cnf(c_0_699, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_698])).
% 12.47/12.65  cnf(c_0_700, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_698])).
% 12.47/12.65  cnf(c_0_701, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X2,X1)|~m2_yellow_6(X2,esk6_0,esk5_1(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_667, c_0_684])).
% 12.47/12.65  cnf(c_0_702, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_699, c_0_100]), c_0_637]), c_0_680]), c_0_700])).
% 12.47/12.65  cnf(c_0_703, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_671, c_0_693])).
% 12.47/12.65  cnf(c_0_704, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_701, c_0_702])).
% 12.47/12.65  cnf(c_0_705, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_702]), c_0_43])).
% 12.47/12.65  cnf(c_0_706, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_703, c_0_702])).
% 12.47/12.65  cnf(c_0_707, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_694])).
% 12.47/12.65  cnf(c_0_708, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_704, c_0_589]), c_0_43]), c_0_705])).
% 12.47/12.65  cnf(c_0_709, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_706, c_0_707])).
% 12.47/12.65  cnf(c_0_710, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_708, c_0_709]), c_0_43])).
% 12.47/12.65  cnf(c_0_711, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_710]), c_0_68])])).
% 12.47/12.65  cnf(c_0_712, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_711]), c_0_24]), c_0_22])]), c_0_25]), c_0_604]), c_0_651]), c_0_686]), c_0_623])).
% 12.47/12.65  cnf(c_0_713, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_712])).
% 12.47/12.65  cnf(c_0_714, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_712])).
% 12.47/12.65  cnf(c_0_715, negated_conjecture, (v4_orders_2(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_30, c_0_604])).
% 12.47/12.65  cnf(c_0_716, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_713, c_0_100]), c_0_637]), c_0_680]), c_0_714])).
% 12.47/12.65  cnf(c_0_717, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_698])).
% 12.47/12.65  cnf(c_0_718, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~v7_waybel_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_55, c_0_715])).
% 12.47/12.65  cnf(c_0_719, negated_conjecture, (v7_waybel_0(esk8_1(esk5_1(esk6_0)))|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_30, c_0_651])).
% 12.47/12.65  cnf(c_0_720, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_681, c_0_716]), c_0_682])).
% 12.47/12.65  cnf(c_0_721, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_717, c_0_100]), c_0_637]), c_0_680]), c_0_700])).
% 12.47/12.65  cnf(c_0_722, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_718, c_0_719])).
% 12.47/12.65  cnf(c_0_723, negated_conjecture, (l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(spm,[status(thm)],[c_0_30, c_0_686])).
% 12.47/12.65  cnf(c_0_724, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_720, c_0_721]), c_0_700])).
% 12.47/12.65  cnf(c_0_725, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~v7_waybel_0(esk8_1(esk5_1(esk6_0)))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_85, c_0_715])).
% 12.47/12.65  cnf(c_0_726, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_722, c_0_723])).
% 12.47/12.65  cnf(c_0_727, negated_conjecture, (r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,X1,esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|~m2_yellow_6(X1,esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_701, c_0_724])).
% 12.47/12.65  cnf(c_0_728, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk5_1(esk6_0),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_724]), c_0_43])).
% 12.47/12.65  cnf(c_0_729, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|~r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_703, c_0_724])).
% 12.47/12.65  cnf(c_0_730, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~l1_waybel_0(esk8_1(esk5_1(esk6_0)),esk6_0)|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_725, c_0_719])).
% 12.47/12.65  cnf(c_0_731, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(spm,[status(thm)],[c_0_81, c_0_726])).
% 12.47/12.65  cnf(c_0_732, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_727, c_0_589]), c_0_43]), c_0_728])).
% 12.47/12.65  cnf(c_0_733, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_729, c_0_707])).
% 12.47/12.65  cnf(c_0_734, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),X1)|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r2_hidden(X1,k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_730, c_0_723]), c_0_731])).
% 12.47/12.65  cnf(c_0_735, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r2_hidden(esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_726])).
% 12.47/12.65  cnf(c_0_736, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_732, c_0_733]), c_0_43])).
% 12.47/12.65  cnf(c_0_737, negated_conjecture, (r3_waybel_9(esk6_0,esk8_1(esk5_1(esk6_0)),esk1_3(u1_struct_0(esk6_0),k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0))|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_734, c_0_735])).
% 12.47/12.65  cnf(c_0_738, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_736]), c_0_68])])).
% 12.47/12.65  cnf(c_0_739, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|r1_tarski(k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_732, c_0_737]), c_0_30])).
% 12.47/12.65  cnf(c_0_740, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_738]), c_0_24]), c_0_22])]), c_0_25]), c_0_604]), c_0_651]), c_0_686]), c_0_623])).
% 12.47/12.65  cnf(c_0_741, negated_conjecture, (k10_yellow_6(esk6_0,esk8_1(esk5_1(esk6_0)))=k1_xboole_0|v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_739]), c_0_68])])).
% 12.47/12.65  cnf(c_0_742, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_740])).
% 12.47/12.65  cnf(c_0_743, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_741]), c_0_24]), c_0_22])]), c_0_25]), c_0_715]), c_0_719]), c_0_723]), c_0_74])).
% 12.47/12.65  cnf(c_0_744, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_740])).
% 12.47/12.65  cnf(c_0_745, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_742, c_0_743]), c_0_637]), c_0_680]), c_0_744])).
% 12.47/12.65  cnf(c_0_746, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_720, c_0_745]), c_0_744])).
% 12.47/12.65  cnf(c_0_747, negated_conjecture, (v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_570]), c_0_258]), c_0_425])).
% 12.47/12.65  cnf(c_0_748, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_570]), c_0_258]), c_0_425])).
% 12.47/12.65  cnf(c_0_749, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_570]), c_0_258]), c_0_425])).
% 12.47/12.65  cnf(c_0_750, negated_conjecture, (v2_struct_0(esk5_1(esk6_0))|v2_struct_0(X1)|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_582, c_0_746])).
% 12.47/12.65  cnf(c_0_751, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_747, c_0_581]), c_0_571])).
% 12.47/12.65  cnf(c_0_752, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_748, c_0_581]), c_0_571])).
% 12.47/12.65  cnf(c_0_753, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_749, c_0_581]), c_0_571])).
% 12.47/12.65  cnf(c_0_754, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_750, c_0_39]), c_0_40]), c_0_41]), c_0_50])).
% 12.47/12.65  cnf(c_0_755, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_751]), c_0_752]), c_0_753])).
% 12.47/12.65  cnf(c_0_756, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_99, c_0_754])).
% 12.47/12.65  cnf(c_0_757, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_576, c_0_755]), c_0_136])).
% 12.47/12.65  cnf(c_0_758, negated_conjecture, (v4_orders_2(X1)|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_38, c_0_754])).
% 12.47/12.65  cnf(c_0_759, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_756, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.65  cnf(c_0_760, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_754]), c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.65  cnf(c_0_761, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_754]), c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.65  cnf(c_0_762, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_754])).
% 12.47/12.65  cnf(c_0_763, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_754])).
% 12.47/12.65  cnf(c_0_764, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_579, c_0_757]), c_0_581])).
% 12.47/12.65  cnf(c_0_765, negated_conjecture, (v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_113, c_0_754])).
% 12.47/12.65  cnf(c_0_766, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v4_orders_2(X1)|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_758, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.65  cnf(c_0_767, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_759, c_0_760]), c_0_761])).
% 12.47/12.65  cnf(c_0_768, negated_conjecture, (v7_waybel_0(X1)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_762, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.65  cnf(c_0_769, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_763, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.65  cnf(c_0_770, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(X1)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_582, c_0_764])).
% 12.47/12.65  cnf(c_0_771, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_743]), c_0_637]), c_0_680]), c_0_744])).
% 12.47/12.65  cnf(c_0_772, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_713, c_0_743]), c_0_637]), c_0_680]), c_0_714])).
% 12.47/12.65  cnf(c_0_773, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_765, c_0_108]), c_0_109]), c_0_110])).
% 12.47/12.65  cnf(c_0_774, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_766, c_0_767])).
% 12.47/12.65  cnf(c_0_775, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_768, c_0_767])).
% 12.47/12.65  cnf(c_0_776, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_769, c_0_767])).
% 12.47/12.65  cnf(c_0_777, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_770, c_0_743]), c_0_637]), c_0_680])).
% 12.47/12.65  cnf(c_0_778, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_771, c_0_772]), c_0_745])).
% 12.47/12.65  cnf(c_0_779, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_773, c_0_760]), c_0_761])).
% 12.47/12.65  cnf(c_0_780, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_774]), c_0_775]), c_0_776])).
% 12.47/12.65  cnf(c_0_781, negated_conjecture, (v2_struct_0(esk8_1(esk5_1(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_777, c_0_778]), c_0_744])).
% 12.47/12.65  cnf(c_0_782, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_779, c_0_780]), c_0_136])).
% 12.47/12.65  cnf(c_0_783, negated_conjecture, (v2_struct_0(X1)|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_582, c_0_781])).
% 12.47/12.65  cnf(c_0_784, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_782]), c_0_767])).
% 12.47/12.65  cnf(c_0_785, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_783, c_0_784])).
% 12.47/12.65  cnf(c_0_786, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_785, c_0_141]), c_0_142])).
% 12.47/12.65  cnf(c_0_787, negated_conjecture, (v1_compts_1(esk6_0)|m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_784]), c_0_32]), c_0_33]), c_0_43])).
% 12.47/12.65  cnf(c_0_788, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_786, c_0_787]), c_0_43]), c_0_101])).
% 12.47/12.65  cnf(c_0_789, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_756, c_0_788])).
% 12.47/12.65  cnf(c_0_790, negated_conjecture, (v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_758, c_0_788])).
% 12.47/12.65  cnf(c_0_791, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_789, c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_792, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_754]), c_0_141]), c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_793, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_754]), c_0_141]), c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_794, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_790, c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_795, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_791, c_0_792]), c_0_793])).
% 12.47/12.65  cnf(c_0_796, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_794, c_0_795])).
% 12.47/12.65  cnf(c_0_797, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_785, c_0_796])).
% 12.47/12.65  cnf(c_0_798, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_797, c_0_159])).
% 12.47/12.65  cnf(c_0_799, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_798, c_0_787]), c_0_43]), c_0_102])).
% 12.47/12.65  cnf(c_0_800, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_789, c_0_799])).
% 12.47/12.65  cnf(c_0_801, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_754]), c_0_142]), c_0_159]), c_0_163])).
% 12.47/12.65  cnf(c_0_802, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_754]), c_0_142]), c_0_159]), c_0_163])).
% 12.47/12.65  cnf(c_0_803, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_790, c_0_799])).
% 12.47/12.65  cnf(c_0_804, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_800, c_0_801]), c_0_802]), c_0_163])).
% 12.47/12.65  cnf(c_0_805, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_803, c_0_804]), c_0_163])).
% 12.47/12.65  cnf(c_0_806, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_797, c_0_805])).
% 12.47/12.65  cnf(c_0_807, negated_conjecture, (v1_compts_1(esk6_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_806, c_0_787]), c_0_43])).
% 12.47/12.65  cnf(c_0_808, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_807])).
% 12.47/12.65  cnf(c_0_809, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_807])).
% 12.47/12.65  cnf(c_0_810, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_807])).
% 12.47/12.65  cnf(c_0_811, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_808, c_0_754]), c_0_788]), c_0_799]), c_0_809])).
% 12.47/12.65  cnf(c_0_812, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_810, c_0_754]), c_0_788]), c_0_799]), c_0_809])).
% 12.47/12.65  cnf(c_0_813, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_800, c_0_811]), c_0_812]), c_0_809])).
% 12.47/12.65  cnf(c_0_814, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_762, c_0_788])).
% 12.47/12.65  cnf(c_0_815, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_763, c_0_788])).
% 12.47/12.65  cnf(c_0_816, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_765, c_0_788])).
% 12.47/12.65  cnf(c_0_817, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_803, c_0_813]), c_0_809])).
% 12.47/12.65  cnf(c_0_818, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_814, c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_819, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_815, c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_820, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_816, c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_821, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|~v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_128, c_0_817])).
% 12.47/12.65  cnf(c_0_822, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_818, c_0_795])).
% 12.47/12.65  cnf(c_0_823, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_819, c_0_795])).
% 12.47/12.65  cnf(c_0_824, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_820, c_0_792]), c_0_793])).
% 12.47/12.65  cnf(c_0_825, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_821, c_0_822]), c_0_823])).
% 12.47/12.65  cnf(c_0_826, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_824, c_0_825]), c_0_136])).
% 12.47/12.65  cnf(c_0_827, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_826]), c_0_795])).
% 12.47/12.65  cnf(c_0_828, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_785, c_0_827])).
% 12.47/12.65  cnf(c_0_829, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_828, c_0_159])).
% 12.47/12.65  cnf(c_0_830, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_829, c_0_787]), c_0_43]), c_0_102])).
% 12.47/12.65  cnf(c_0_831, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_789, c_0_830])).
% 12.47/12.65  cnf(c_0_832, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_814, c_0_830])).
% 12.47/12.65  cnf(c_0_833, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_831, c_0_801]), c_0_802]), c_0_163])).
% 12.47/12.65  cnf(c_0_834, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_832, c_0_833]), c_0_163])).
% 12.47/12.65  cnf(c_0_835, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_828, c_0_834])).
% 12.47/12.65  cnf(c_0_836, negated_conjecture, (v1_compts_1(esk6_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_835, c_0_787]), c_0_43])).
% 12.47/12.65  cnf(c_0_837, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_836])).
% 12.47/12.65  cnf(c_0_838, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_836])).
% 12.47/12.65  cnf(c_0_839, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_836])).
% 12.47/12.65  cnf(c_0_840, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_837, c_0_754]), c_0_788]), c_0_830]), c_0_838])).
% 12.47/12.65  cnf(c_0_841, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_839, c_0_754]), c_0_788]), c_0_830]), c_0_838])).
% 12.47/12.65  cnf(c_0_842, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_831, c_0_840]), c_0_841]), c_0_838])).
% 12.47/12.65  cnf(c_0_843, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_832, c_0_842]), c_0_838])).
% 12.47/12.65  cnf(c_0_844, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_815, c_0_830])).
% 12.47/12.65  cnf(c_0_845, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_816, c_0_830])).
% 12.47/12.65  cnf(c_0_846, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_821, c_0_843])).
% 12.47/12.65  cnf(c_0_847, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_844, c_0_833]), c_0_163])).
% 12.47/12.65  cnf(c_0_848, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_845, c_0_801]), c_0_802]), c_0_163])).
% 12.47/12.65  cnf(c_0_849, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_846, c_0_847])).
% 12.47/12.65  cnf(c_0_850, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_848, c_0_849]), c_0_136])).
% 12.47/12.65  cnf(c_0_851, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_216, c_0_850]), c_0_833])).
% 12.47/12.65  cnf(c_0_852, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_828, c_0_851])).
% 12.47/12.65  cnf(c_0_853, negated_conjecture, (v1_compts_1(esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_852, c_0_787]), c_0_43])).
% 12.47/12.65  cnf(c_0_854, negated_conjecture, (v4_orders_2(esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_30, c_0_853])).
% 12.47/12.65  cnf(c_0_855, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|~v2_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_103, c_0_853])).
% 12.47/12.65  cnf(c_0_856, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_104, c_0_853])).
% 12.47/12.65  cnf(c_0_857, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_105, c_0_853])).
% 12.47/12.65  cnf(c_0_858, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_854]), c_0_788]), c_0_830]), c_0_855])).
% 12.47/12.65  cnf(c_0_859, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_856, c_0_854]), c_0_788]), c_0_830]), c_0_855])).
% 12.47/12.65  cnf(c_0_860, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_857, c_0_854]), c_0_788]), c_0_830]), c_0_855])).
% 12.47/12.65  cnf(c_0_861, negated_conjecture, (l1_waybel_0(X1,esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_854]), c_0_788]), c_0_830]), c_0_855])).
% 12.47/12.65  cnf(c_0_862, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_858, c_0_859]), c_0_860])).
% 12.47/12.65  cnf(c_0_863, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|r2_hidden(X1,k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,X1)))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_854]), c_0_788]), c_0_830]), c_0_855])).
% 12.47/12.65  cnf(c_0_864, negated_conjecture, (l1_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_861, c_0_862])).
% 12.47/12.65  cnf(c_0_865, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|r2_hidden(esk3_2(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_863, c_0_859]), c_0_860])).
% 12.47/12.65  cnf(c_0_866, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_846, c_0_864])).
% 12.47/12.65  cnf(c_0_867, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|~v3_yellow_6(X1,esk6_0)|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_853])).
% 12.47/12.65  cnf(c_0_868, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_865, c_0_866]), c_0_136])).
% 12.47/12.65  cnf(c_0_869, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_867, c_0_868]), c_0_862])).
% 12.47/12.65  cnf(c_0_870, negated_conjecture, (v2_struct_0(esk5_1(esk6_0))|v2_struct_0(X1)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_582, c_0_869])).
% 12.47/12.65  cnf(c_0_871, negated_conjecture, (v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)|~v7_waybel_0(esk7_0)), inference(spm,[status(thm)],[c_0_870, c_0_754])).
% 12.47/12.65  cnf(c_0_872, negated_conjecture, (v4_orders_2(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_871, c_0_108]), c_0_109]), c_0_767]), c_0_110])).
% 12.47/12.65  cnf(c_0_873, negated_conjecture, (v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)|~v7_waybel_0(esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_783, c_0_872])).
% 12.47/12.65  cnf(c_0_874, negated_conjecture, (v7_waybel_0(esk7_0)|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_873, c_0_141]), c_0_142])).
% 12.47/12.65  cnf(c_0_875, negated_conjecture, (v1_compts_1(esk6_0)|m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_872]), c_0_32]), c_0_33]), c_0_43])).
% 12.47/12.65  cnf(c_0_876, negated_conjecture, (v7_waybel_0(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_874, c_0_875]), c_0_43]), c_0_101])).
% 12.47/12.65  cnf(c_0_877, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~l1_waybel_0(esk7_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_756, c_0_876])])).
% 12.47/12.65  cnf(c_0_878, negated_conjecture, (v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|~l1_waybel_0(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_871, c_0_876])])).
% 12.47/12.65  cnf(c_0_879, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_877, c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_880, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_878, c_0_147]), c_0_148])).
% 12.47/12.65  cnf(c_0_881, negated_conjecture, (v7_waybel_0(esk5_1(esk6_0))|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_879, c_0_792]), c_0_793]), c_0_880])).
% 12.47/12.65  cnf(c_0_882, negated_conjecture, (v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))|~l1_waybel_0(esk5_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_873, c_0_881])).
% 12.47/12.65  cnf(c_0_883, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)|v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_882, c_0_159])).
% 12.47/12.65  cnf(c_0_884, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_883, c_0_875]), c_0_43]), c_0_102])).
% 12.47/12.65  cnf(c_0_885, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_877, c_0_884])])).
% 12.47/12.65  cnf(c_0_886, negated_conjecture, (v4_orders_2(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_854]), c_0_788]), c_0_830]), c_0_855])).
% 12.47/12.65  cnf(c_0_887, negated_conjecture, (v7_waybel_0(X1)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|~m2_yellow_6(X1,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_854]), c_0_788]), c_0_830]), c_0_855])).
% 12.47/12.65  cnf(c_0_888, negated_conjecture, (v2_struct_0(esk5_1(esk6_0))|v2_struct_0(esk7_0)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_878, c_0_884])])).
% 12.47/12.65  cnf(c_0_889, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)|l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_885, c_0_801]), c_0_802]), c_0_163])).
% 12.47/12.65  cnf(c_0_890, negated_conjecture, (v4_orders_2(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_886, c_0_862])).
% 12.47/12.65  cnf(c_0_891, negated_conjecture, (v7_waybel_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_887, c_0_862])).
% 12.47/12.65  cnf(c_0_892, negated_conjecture, (l1_waybel_0(esk5_1(esk6_0),esk6_0)|v2_struct_0(esk5_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_888, c_0_889]), c_0_163])).
% 12.47/12.65  cnf(c_0_893, negated_conjecture, (k10_yellow_6(esk6_0,esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))=k1_xboole_0|v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_890]), c_0_891]), c_0_864])).
% 12.47/12.65  cnf(c_0_894, negated_conjecture, (v2_struct_0(esk5_1(esk6_0))|~m2_yellow_6(esk8_1(esk5_1(esk6_0)),esk6_0,esk5_1(esk6_0))), inference(spm,[status(thm)],[c_0_882, c_0_892])).
% 12.47/12.65  cnf(c_0_895, negated_conjecture, (v3_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0)|v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_865, c_0_893]), c_0_136])).
% 12.47/12.65  cnf(c_0_896, negated_conjecture, (v1_compts_1(esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_894, c_0_875]), c_0_43])).
% 12.47/12.65  cnf(c_0_897, negated_conjecture, (v2_struct_0(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_867, c_0_895]), c_0_862])).
% 12.47/12.65  cnf(c_0_898, negated_conjecture, (v4_orders_2(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_896])])).
% 12.47/12.65  cnf(c_0_899, negated_conjecture, (~v2_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_896])])).
% 12.47/12.65  cnf(c_0_900, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_896])])).
% 12.47/12.65  cnf(c_0_901, negated_conjecture, (r3_waybel_9(esk6_0,X1,esk3_2(esk6_0,X1))|v2_struct_0(X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_896])])).
% 12.47/12.65  cnf(c_0_902, negated_conjecture, (v2_struct_0(X1)|~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,X1)|~l1_waybel_0(X1,esk6_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_582, c_0_897])).
% 12.47/12.65  cnf(c_0_903, negated_conjecture, (m2_yellow_6(esk2_3(esk6_0,esk7_0,X1),esk6_0,esk7_0)|~r3_waybel_9(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_898]), c_0_884]), c_0_876])]), c_0_899])).
% 12.47/12.65  cnf(c_0_904, negated_conjecture, (m1_subset_1(esk3_2(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_900, c_0_898]), c_0_884]), c_0_876])]), c_0_899])).
% 12.47/12.65  cnf(c_0_905, negated_conjecture, (r3_waybel_9(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_901, c_0_898]), c_0_884]), c_0_876])]), c_0_899])).
% 12.47/12.65  cnf(c_0_906, negated_conjecture, (~m2_yellow_6(esk2_3(esk6_0,esk7_0,esk3_2(esk6_0,esk7_0)),esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_902, c_0_898]), c_0_884]), c_0_876])]), c_0_899])).
% 12.47/12.65  cnf(c_0_907, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_903, c_0_904]), c_0_905])]), c_0_906]), ['proof']).
% 12.47/12.65  # SZS output end CNFRefutation
% 12.47/12.65  # Proof object total steps             : 908
% 12.47/12.65  # Proof object clause steps            : 875
% 12.47/12.65  # Proof object formula steps           : 33
% 12.47/12.65  # Proof object conjectures             : 849
% 12.47/12.65  # Proof object clause conjectures      : 846
% 12.47/12.65  # Proof object formula conjectures     : 3
% 12.47/12.65  # Proof object initial clauses used    : 36
% 12.47/12.65  # Proof object initial formulas used   : 16
% 12.47/12.65  # Proof object generating inferences   : 831
% 12.47/12.65  # Proof object simplifying inferences  : 994
% 12.47/12.65  # Training examples: 0 positive, 0 negative
% 12.47/12.65  # Parsed axioms                        : 16
% 12.47/12.65  # Removed by relevancy pruning/SinE    : 0
% 12.47/12.65  # Initial clauses                      : 42
% 12.47/12.65  # Removed in clause preprocessing      : 0
% 12.47/12.65  # Initial clauses in saturation        : 42
% 12.47/12.65  # Processed clauses                    : 68109
% 12.47/12.65  # ...of these trivial                  : 21
% 12.47/12.65  # ...subsumed                          : 50377
% 12.47/12.65  # ...remaining for further processing  : 17711
% 12.47/12.65  # Other redundant clauses eliminated   : 2
% 12.47/12.65  # Clauses deleted for lack of memory   : 0
% 12.47/12.65  # Backward-subsumed                    : 17365
% 12.47/12.65  # Backward-rewritten                   : 189
% 12.47/12.65  # Generated clauses                    : 243767
% 12.47/12.65  # ...of the previous two non-trivial   : 226021
% 12.47/12.65  # Contextual simplify-reflections      : 10435
% 12.47/12.65  # Paramodulations                      : 243736
% 12.47/12.65  # Factorizations                       : 0
% 12.47/12.65  # Equation resolutions                 : 2
% 12.47/12.65  # Propositional unsat checks           : 0
% 12.47/12.65  #    Propositional check models        : 0
% 12.47/12.65  #    Propositional check unsatisfiable : 0
% 12.47/12.65  #    Propositional clauses             : 0
% 12.47/12.65  #    Propositional clauses after purity: 0
% 12.47/12.65  #    Propositional unsat core size     : 0
% 12.47/12.65  #    Propositional preprocessing time  : 0.000
% 12.47/12.65  #    Propositional encoding time       : 0.000
% 12.47/12.65  #    Propositional solver time         : 0.000
% 12.47/12.65  #    Success case prop preproc time    : 0.000
% 12.47/12.65  #    Success case prop encoding time   : 0.000
% 12.47/12.65  #    Success case prop solver time     : 0.000
% 12.47/12.65  # Current number of processed clauses  : 85
% 12.47/12.65  #    Positive orientable unit clauses  : 16
% 12.47/12.65  #    Positive unorientable unit clauses: 0
% 12.47/12.65  #    Negative unit clauses             : 7
% 12.47/12.65  #    Non-unit-clauses                  : 62
% 12.47/12.65  # Current number of unprocessed clauses: 272
% 12.47/12.65  # ...number of literals in the above   : 2111
% 12.47/12.65  # Current number of archived formulas  : 0
% 12.47/12.65  # Current number of archived clauses   : 17624
% 12.47/12.65  # Clause-clause subsumption calls (NU) : 28135197
% 12.47/12.65  # Rec. Clause-clause subsumption calls : 105687
% 12.47/12.65  # Non-unit clause-clause subsumptions  : 74529
% 12.47/12.65  # Unit Clause-clause subsumption calls : 739
% 12.47/12.65  # Rewrite failures with RHS unbound    : 0
% 12.47/12.65  # BW rewrite match attempts            : 10
% 12.47/12.65  # BW rewrite match successes           : 7
% 12.47/12.65  # Condensation attempts                : 0
% 12.47/12.65  # Condensation successes               : 0
% 12.47/12.65  # Termbank termtop insertions          : 14203702
% 12.47/12.66  
% 12.47/12.66  # -------------------------------------------------
% 12.47/12.66  # User time                : 12.255 s
% 12.47/12.66  # System time              : 0.056 s
% 12.47/12.66  # Total time               : 12.311 s
% 12.47/12.66  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
