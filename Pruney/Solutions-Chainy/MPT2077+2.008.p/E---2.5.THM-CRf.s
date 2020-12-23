%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:07 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  142 (871727 expanded)
%              Number of clauses        :  109 (287543 expanded)
%              Number of leaves         :   16 (216418 expanded)
%              Depth                    :   29
%              Number of atoms          :  893 (9885284 expanded)
%              Number of equality atoms :   34 (17076 expanded)
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

fof(l38_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ~ ( r2_hidden(X2,k6_yellow_6(X1))
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r3_waybel_9(X1,X2,X3) ) ) )
       => v1_compts_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_yellow19)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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
    ! [X51,X53] :
      ( ( ~ v2_struct_0(esk7_1(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( v4_orders_2(esk7_1(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( v7_waybel_0(esk7_1(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( l1_waybel_0(esk7_1(X51),X51)
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( r2_hidden(esk7_1(X51),k6_yellow_6(X51))
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) )
      & ( ~ m1_subset_1(X53,u1_struct_0(X51))
        | ~ r3_waybel_9(X51,esk7_1(X51),X53)
        | v1_compts_1(X51)
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_yellow19])])])])])])).

fof(c_0_18,negated_conjecture,(
    ! [X56,X57] :
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
      & ( ~ m2_yellow_6(X56,esk8_0,esk9_0)
        | ~ v3_yellow_6(X56,esk8_0)
        | ~ v1_compts_1(esk8_0) )
      & ( m2_yellow_6(esk10_1(X57),esk8_0,X57)
        | v2_struct_0(X57)
        | ~ v4_orders_2(X57)
        | ~ v7_waybel_0(X57)
        | ~ l1_waybel_0(X57,esk8_0)
        | v1_compts_1(esk8_0) )
      & ( v3_yellow_6(esk10_1(X57),esk8_0)
        | v2_struct_0(X57)
        | ~ v4_orders_2(X57)
        | ~ v7_waybel_0(X57)
        | ~ l1_waybel_0(X57,esk8_0)
        | v1_compts_1(esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

cnf(c_0_19,plain,
    ( l1_waybel_0(esk7_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v4_orders_2(esk7_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v7_waybel_0(esk7_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v2_struct_0(X34)
        | ~ m2_yellow_6(X34,X32,X33)
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32)
        | v2_struct_0(X33)
        | ~ v4_orders_2(X33)
        | ~ v7_waybel_0(X33)
        | ~ l1_waybel_0(X33,X32) )
      & ( v4_orders_2(X34)
        | ~ m2_yellow_6(X34,X32,X33)
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32)
        | v2_struct_0(X33)
        | ~ v4_orders_2(X33)
        | ~ v7_waybel_0(X33)
        | ~ l1_waybel_0(X33,X32) )
      & ( v7_waybel_0(X34)
        | ~ m2_yellow_6(X34,X32,X33)
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32)
        | v2_struct_0(X33)
        | ~ v4_orders_2(X33)
        | ~ v7_waybel_0(X33)
        | ~ l1_waybel_0(X33,X32) )
      & ( l1_waybel_0(X34,X32)
        | ~ m2_yellow_6(X34,X32,X33)
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32)
        | v2_struct_0(X33)
        | ~ v4_orders_2(X33)
        | ~ v7_waybel_0(X33)
        | ~ l1_waybel_0(X33,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_26,negated_conjecture,
    ( m2_yellow_6(esk10_1(X1),esk8_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk8_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | l1_waybel_0(esk7_1(esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v4_orders_2(esk7_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v7_waybel_0(esk7_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_21])]),c_0_22])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_31,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_32,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v4_orders_2(X31)
      | ~ v7_waybel_0(X31)
      | ~ l1_waybel_0(X31,X30)
      | m1_subset_1(k10_yellow_6(X30,X31),k1_zfmisc_1(u1_struct_0(X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_33,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | m2_yellow_6(esk10_1(esk7_1(esk8_0)),esk8_0,esk7_1(esk8_0))
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

fof(c_0_35,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_36,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_22]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_44,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34]),c_0_22]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v7_waybel_0(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_22]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | ~ v2_struct_0(esk10_1(esk7_1(esk8_0)))
    | ~ l1_struct_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_22]),c_0_28]),c_0_29]),c_0_27])).

fof(c_0_48,plain,(
    ! [X21,X22,X23,X24,X25,X29] :
      ( ( ~ r2_hidden(X24,X23)
        | ~ m1_connsp_2(X25,X21,X24)
        | r1_waybel_0(X21,X22,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | X23 != k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_connsp_2(esk2_4(X21,X22,X23,X24),X21,X24)
        | r2_hidden(X24,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | X23 != k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_waybel_0(X21,X22,esk2_4(X21,X22,X23,X24))
        | r2_hidden(X24,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | X23 != k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk3_3(X21,X22,X23),u1_struct_0(X21))
        | X23 = k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_connsp_2(esk4_3(X21,X22,X23),X21,esk3_3(X21,X22,X23))
        | ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_waybel_0(X21,X22,esk4_3(X21,X22,X23))
        | ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk3_3(X21,X22,X23),X23)
        | ~ m1_connsp_2(X29,X21,esk3_3(X21,X22,X23))
        | r1_waybel_0(X21,X22,X29)
        | X23 = k10_yellow_6(X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_49,plain,(
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | v2_struct_0(X38)
      | ~ v4_orders_2(X38)
      | ~ v7_waybel_0(X38)
      | ~ l1_waybel_0(X38,X37)
      | ~ m1_subset_1(X39,u1_struct_0(X37))
      | ~ r2_hidden(X39,k10_yellow_6(X37,X38))
      | r3_waybel_9(X37,X38,X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | m1_subset_1(k10_yellow_6(esk8_0,esk7_1(esk8_0)),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_20]),c_0_21])]),c_0_22]),c_0_28]),c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_21])])).

cnf(c_0_55,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v4_orders_2(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_44]),c_0_21])])).

cnf(c_0_56,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v7_waybel_0(esk10_1(esk7_1(esk8_0)))
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_21])])).

cnf(c_0_57,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | ~ v2_struct_0(esk10_1(esk7_1(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_44]),c_0_21])])).

cnf(c_0_58,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k10_yellow_6(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_59,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_60,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( m1_subset_1(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | r1_tarski(k10_yellow_6(esk8_0,esk7_1(esk8_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | m1_subset_1(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_54]),c_0_20]),c_0_21])]),c_0_22]),c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_64,plain,
    ( X1 = k10_yellow_6(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_subset_1(esk3_3(X2,X3,X1),u1_struct_0(X2))
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_40])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
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
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | m1_subset_1(esk1_2(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1),u1_struct_0(esk8_0))
    | r1_tarski(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_68,plain,(
    ! [X40,X41,X42,X43] :
      ( v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X41)
      | ~ v4_orders_2(X41)
      | ~ v7_waybel_0(X41)
      | ~ l1_waybel_0(X41,X40)
      | ~ m2_yellow_6(X42,X40,X41)
      | ~ m1_subset_1(X43,u1_struct_0(X40))
      | ~ r3_waybel_9(X40,X42,X43)
      | r3_waybel_9(X40,X41,X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

cnf(c_0_69,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_63])).

cnf(c_0_70,plain,
    ( m1_connsp_2(esk2_4(X1,X2,X3,X4),X1,X4)
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
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_71,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(X1,X2,k1_xboole_0),u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_72,plain,(
    ! [X18,X19] :
      ( ~ r2_hidden(X18,X19)
      | ~ r1_tarski(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_73,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk7_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | r3_waybel_9(esk8_0,esk7_1(esk8_0),esk1_2(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1))
    | v2_struct_0(esk7_1(esk8_0))
    | r1_tarski(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_20]),c_0_21])]),c_0_22]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_75,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | m1_subset_1(esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1),u1_struct_0(esk8_0))
    | r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_69])).

cnf(c_0_77,plain,
    ( m1_connsp_2(esk2_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_70]),c_0_42])).

cnf(c_0_78,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk7_1(esk8_0)) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | m1_subset_1(esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_27]),c_0_20]),c_0_21])]),c_0_22]),c_0_28]),c_0_29])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | r1_tarski(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_20]),c_0_21])]),c_0_22]),c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | r3_waybel_9(esk8_0,X1,esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2))
    | v2_struct_0(esk7_1(esk8_0))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2)
    | ~ r3_waybel_9(esk8_0,X3,esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2))
    | ~ m2_yellow_6(X3,esk8_0,X1)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_82,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | r3_waybel_9(esk8_0,esk10_1(esk7_1(esk8_0)),esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1))
    | v2_struct_0(esk7_1(esk8_0))
    | r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_76]),c_0_20]),c_0_21])]),c_0_22]),c_0_55]),c_0_56]),c_0_54]),c_0_57])).

cnf(c_0_83,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk7_1(esk8_0)) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | m1_connsp_2(esk2_4(esk8_0,X1,k10_yellow_6(esk8_0,X1),esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0)),esk8_0,esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0))
    | v2_struct_0(esk7_1(esk8_0))
    | v2_struct_0(X1)
    | r2_hidden(esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0),k10_yellow_6(esk8_0,X1))
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_84,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk8_0,esk7_1(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | r3_waybel_9(esk8_0,X1,esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2))
    | v2_struct_0(esk7_1(esk8_0))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2)
    | ~ m2_yellow_6(esk10_1(esk7_1(esk8_0)),esk8_0,X1)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r1_waybel_0(X1,X2,X4)
    | X3 = k10_yellow_6(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X4,X1,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_87,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk7_1(esk8_0)) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | m1_connsp_2(esk2_4(esk8_0,esk7_1(esk8_0),k10_yellow_6(esk8_0,esk7_1(esk8_0)),esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0)),esk8_0,esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0))
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_27]),c_0_28]),c_0_29]),c_0_84])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_65])).

cnf(c_0_89,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | r3_waybel_9(esk8_0,esk7_1(esk8_0),esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1))
    | v2_struct_0(esk7_1(esk8_0))
    | r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_34]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_90,plain,
    ( r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_91,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk7_1(esk8_0)) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | r1_waybel_0(esk8_0,esk7_1(esk8_0),esk2_4(esk8_0,esk7_1(esk8_0),k10_yellow_6(esk8_0,esk7_1(esk8_0)),esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0)))
    | v2_struct_0(esk7_1(esk8_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_20]),c_0_21])]),c_0_22]),c_0_88]),c_0_28]),c_0_29]),c_0_27])).

cnf(c_0_92,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | m1_subset_1(esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_54]),c_0_20]),c_0_21])]),c_0_22]),c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_93,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_89]),c_0_20]),c_0_21])]),c_0_22]),c_0_76])).

cnf(c_0_94,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(X3,k10_yellow_6(X2,X1))
    | ~ r1_waybel_0(X2,X1,esk2_4(X2,X1,k10_yellow_6(X2,X1),X3))
    | ~ l1_waybel_0(X1,X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_90]),c_0_42])).

cnf(c_0_95,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk7_1(esk8_0)) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | r1_waybel_0(esk8_0,esk7_1(esk8_0),esk2_4(esk8_0,esk7_1(esk8_0),k10_yellow_6(esk8_0,esk7_1(esk8_0)),esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0)))
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_40]),c_0_65])])).

cnf(c_0_96,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | m1_connsp_2(esk2_4(esk8_0,X1,k10_yellow_6(esk8_0,X1),esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0)),esk8_0,esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0))
    | v2_struct_0(esk7_1(esk8_0))
    | v2_struct_0(X1)
    | r2_hidden(esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),k10_yellow_6(esk8_0,X1))
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_92]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_97,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk7_1(esk8_0)) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_20]),c_0_21])]),c_0_22]),c_0_78]),c_0_28]),c_0_29]),c_0_27]),c_0_84])).

cnf(c_0_99,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | m1_connsp_2(esk2_4(esk8_0,esk10_1(esk7_1(esk8_0)),k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0)),esk8_0,esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0))
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_54]),c_0_55]),c_0_56]),c_0_97]),c_0_57])).

cnf(c_0_100,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_98])).

fof(c_0_101,plain,(
    ! [X35,X36] :
      ( ( ~ v3_yellow_6(X36,X35)
        | k10_yellow_6(X35,X36) != k1_xboole_0
        | v2_struct_0(X36)
        | ~ v4_orders_2(X36)
        | ~ v7_waybel_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( k10_yellow_6(X35,X36) = k1_xboole_0
        | v3_yellow_6(X36,X35)
        | v2_struct_0(X36)
        | ~ v4_orders_2(X36)
        | ~ v7_waybel_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

cnf(c_0_102,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | r1_waybel_0(esk8_0,esk10_1(esk7_1(esk8_0)),esk2_4(esk8_0,esk10_1(esk7_1(esk8_0)),k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0)))
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_99]),c_0_20]),c_0_21])]),c_0_22]),c_0_88]),c_0_100]),c_0_55]),c_0_56]),c_0_54]),c_0_57])).

cnf(c_0_103,negated_conjecture,
    ( k10_yellow_6(esk8_0,X1) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(esk8_0,X1,k1_xboole_0),u1_struct_0(esk8_0))
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_100]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_104,negated_conjecture,
    ( v3_yellow_6(esk10_1(X1),esk8_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk8_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_105,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))) = k1_xboole_0
    | v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_102]),c_0_20]),c_0_21])]),c_0_22]),c_0_103]),c_0_55]),c_0_56]),c_0_54]),c_0_97]),c_0_57])).

cnf(c_0_107,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v3_yellow_6(esk10_1(esk7_1(esk8_0)),esk8_0)
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_108,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk7_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_109,negated_conjecture,
    ( v1_compts_1(esk8_0)
    | v2_struct_0(esk7_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_20]),c_0_21])]),c_0_22]),c_0_55]),c_0_56]),c_0_54]),c_0_107]),c_0_57])).

fof(c_0_110,plain,(
    ! [X48,X49] :
      ( ( m1_subset_1(esk6_2(X48,X49),u1_struct_0(X48))
        | v2_struct_0(X49)
        | ~ v4_orders_2(X49)
        | ~ v7_waybel_0(X49)
        | ~ l1_waybel_0(X49,X48)
        | ~ v1_compts_1(X48)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( r3_waybel_9(X48,X49,esk6_2(X48,X49))
        | v2_struct_0(X49)
        | ~ v4_orders_2(X49)
        | ~ v7_waybel_0(X49)
        | ~ l1_waybel_0(X49,X48)
        | ~ v1_compts_1(X48)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).

cnf(c_0_111,negated_conjecture,
    ( l1_waybel_0(esk9_0,esk8_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_112,negated_conjecture,
    ( v1_compts_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_113,negated_conjecture,
    ( v7_waybel_0(esk9_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_114,negated_conjecture,
    ( v4_orders_2(esk9_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_115,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_116,plain,(
    ! [X44,X45,X46] :
      ( ( m2_yellow_6(esk5_3(X44,X45,X46),X44,X45)
        | ~ r3_waybel_9(X44,X45,X46)
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | v2_struct_0(X45)
        | ~ v4_orders_2(X45)
        | ~ v7_waybel_0(X45)
        | ~ l1_waybel_0(X45,X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( r2_hidden(X46,k10_yellow_6(X44,esk5_3(X44,X45,X46)))
        | ~ r3_waybel_9(X44,X45,X46)
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | v2_struct_0(X45)
        | ~ v4_orders_2(X45)
        | ~ v7_waybel_0(X45)
        | ~ l1_waybel_0(X45,X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

cnf(c_0_117,plain,
    ( m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_118,negated_conjecture,
    ( l1_waybel_0(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112])])).

cnf(c_0_119,negated_conjecture,
    ( v7_waybel_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_112])])).

cnf(c_0_120,negated_conjecture,
    ( v4_orders_2(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_112])])).

cnf(c_0_121,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_112])])).

cnf(c_0_122,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_112]),c_0_119]),c_0_120]),c_0_20]),c_0_21])]),c_0_121]),c_0_22])).

cnf(c_0_124,plain,
    ( r3_waybel_9(X1,X2,esk6_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_125,negated_conjecture,
    ( m2_yellow_6(esk5_3(esk8_0,X1,esk6_2(esk8_0,esk9_0)),esk8_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_126,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_118]),c_0_112]),c_0_119]),c_0_120]),c_0_20]),c_0_21])]),c_0_121]),c_0_22])).

cnf(c_0_127,negated_conjecture,
    ( m2_yellow_6(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)),esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_118]),c_0_119]),c_0_120])]),c_0_121])).

cnf(c_0_128,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_129,negated_conjecture,
    ( l1_waybel_0(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)),esk8_0)
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_127]),c_0_118]),c_0_119]),c_0_120])]),c_0_121]),c_0_22])).

cnf(c_0_130,negated_conjecture,
    ( v4_orders_2(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_127]),c_0_118]),c_0_119]),c_0_120])]),c_0_121]),c_0_22])).

cnf(c_0_131,negated_conjecture,
    ( v7_waybel_0(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_127]),c_0_118]),c_0_119]),c_0_120])]),c_0_121]),c_0_22])).

cnf(c_0_132,negated_conjecture,
    ( ~ v2_struct_0(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_127]),c_0_118]),c_0_119]),c_0_120])]),c_0_121]),c_0_22])).

cnf(c_0_133,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_134,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk8_0,esk9_0)
    | ~ v3_yellow_6(X1,esk8_0)
    | ~ v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_135,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))) = k1_xboole_0
    | v3_yellow_6(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)),esk8_0)
    | ~ l1_struct_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_20]),c_0_21])]),c_0_22]),c_0_130]),c_0_131]),c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk6_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk5_3(esk8_0,X1,esk6_2(esk8_0,esk9_0))))
    | ~ r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_123]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_137,negated_conjecture,
    ( ~ v3_yellow_6(X1,esk8_0)
    | ~ m2_yellow_6(X1,esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_112])])).

cnf(c_0_138,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))) = k1_xboole_0
    | v3_yellow_6(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_44]),c_0_21])])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(esk6_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_126]),c_0_118]),c_0_119]),c_0_120])]),c_0_121])).

cnf(c_0_140,negated_conjecture,
    ( k10_yellow_6(esk8_0,esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_127])])).

cnf(c_0_141,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_140]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.77/0.97  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.77/0.97  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.77/0.97  #
% 0.77/0.97  # Preprocessing time       : 0.030 s
% 0.77/0.97  # Presaturation interreduction done
% 0.77/0.97  
% 0.77/0.97  # Proof found!
% 0.77/0.97  # SZS status Theorem
% 0.77/0.97  # SZS output start CNFRefutation
% 0.77/0.97  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow19)).
% 0.77/0.97  fof(l38_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>~((r2_hidden(X2,k6_yellow_6(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r3_waybel_9(X1,X2,X3))))))=>v1_compts_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_yellow19)).
% 0.77/0.97  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.77/0.97  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.77/0.97  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.77/0.97  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.77/0.97  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.77/0.97  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.77/0.97  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.77/0.97  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.77/0.97  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.77/0.97  fof(t31_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_waybel_9(X1,X3,X4)=>r3_waybel_9(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_waybel_9)).
% 0.77/0.97  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.77/0.97  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.77/0.97  fof(l37_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l37_yellow19)).
% 0.77/0.97  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.77/0.97  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.77/0.97  fof(c_0_17, plain, ![X51, X53]:(((((~v2_struct_0(esk7_1(X51))|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)))&(v4_orders_2(esk7_1(X51))|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))))&(v7_waybel_0(esk7_1(X51))|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))))&(l1_waybel_0(esk7_1(X51),X51)|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))))&((r2_hidden(esk7_1(X51),k6_yellow_6(X51))|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)))&(~m1_subset_1(X53,u1_struct_0(X51))|~r3_waybel_9(X51,esk7_1(X51),X53)|v1_compts_1(X51)|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_yellow19])])])])])])).
% 0.77/0.97  fof(c_0_18, negated_conjecture, ![X56, X57]:(((~v2_struct_0(esk8_0)&v2_pre_topc(esk8_0))&l1_pre_topc(esk8_0))&((((((~v2_struct_0(esk9_0)|~v1_compts_1(esk8_0))&(v4_orders_2(esk9_0)|~v1_compts_1(esk8_0)))&(v7_waybel_0(esk9_0)|~v1_compts_1(esk8_0)))&(l1_waybel_0(esk9_0,esk8_0)|~v1_compts_1(esk8_0)))&(~m2_yellow_6(X56,esk8_0,esk9_0)|~v3_yellow_6(X56,esk8_0)|~v1_compts_1(esk8_0)))&((m2_yellow_6(esk10_1(X57),esk8_0,X57)|(v2_struct_0(X57)|~v4_orders_2(X57)|~v7_waybel_0(X57)|~l1_waybel_0(X57,esk8_0))|v1_compts_1(esk8_0))&(v3_yellow_6(esk10_1(X57),esk8_0)|(v2_struct_0(X57)|~v4_orders_2(X57)|~v7_waybel_0(X57)|~l1_waybel_0(X57,esk8_0))|v1_compts_1(esk8_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).
% 0.77/0.97  cnf(c_0_19, plain, (l1_waybel_0(esk7_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.97  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.97  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.97  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.97  cnf(c_0_23, plain, (v4_orders_2(esk7_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.97  cnf(c_0_24, plain, (v7_waybel_0(esk7_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.97  fof(c_0_25, plain, ![X32, X33, X34]:((((~v2_struct_0(X34)|~m2_yellow_6(X34,X32,X33)|(v2_struct_0(X32)|~l1_struct_0(X32)|v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32)))&(v4_orders_2(X34)|~m2_yellow_6(X34,X32,X33)|(v2_struct_0(X32)|~l1_struct_0(X32)|v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32))))&(v7_waybel_0(X34)|~m2_yellow_6(X34,X32,X33)|(v2_struct_0(X32)|~l1_struct_0(X32)|v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32))))&(l1_waybel_0(X34,X32)|~m2_yellow_6(X34,X32,X33)|(v2_struct_0(X32)|~l1_struct_0(X32)|v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.77/0.97  cnf(c_0_26, negated_conjecture, (m2_yellow_6(esk10_1(X1),esk8_0,X1)|v2_struct_0(X1)|v1_compts_1(esk8_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.97  cnf(c_0_27, negated_conjecture, (v1_compts_1(esk8_0)|l1_waybel_0(esk7_1(esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.97  cnf(c_0_28, negated_conjecture, (v1_compts_1(esk8_0)|v4_orders_2(esk7_1(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.97  cnf(c_0_29, negated_conjecture, (v1_compts_1(esk8_0)|v7_waybel_0(esk7_1(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.97  fof(c_0_30, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.77/0.97  fof(c_0_31, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.77/0.97  fof(c_0_32, plain, ![X30, X31]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30)|m1_subset_1(k10_yellow_6(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.77/0.97  cnf(c_0_33, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.97  cnf(c_0_34, negated_conjecture, (v1_compts_1(esk8_0)|m2_yellow_6(esk10_1(esk7_1(esk8_0)),esk8_0,esk7_1(esk8_0))|v2_struct_0(esk7_1(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.77/0.97  fof(c_0_35, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.77/0.97  cnf(c_0_36, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.97  cnf(c_0_37, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.97  cnf(c_0_38, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.97  cnf(c_0_39, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.77/0.97  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.77/0.97  fof(c_0_41, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.77/0.97  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.97  cnf(c_0_43, negated_conjecture, (v1_compts_1(esk8_0)|l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)|v2_struct_0(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_22]), c_0_28]), c_0_29]), c_0_27])).
% 0.77/0.97  cnf(c_0_44, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.77/0.97  cnf(c_0_45, negated_conjecture, (v1_compts_1(esk8_0)|v4_orders_2(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_34]), c_0_22]), c_0_28]), c_0_29]), c_0_27])).
% 0.77/0.97  cnf(c_0_46, negated_conjecture, (v1_compts_1(esk8_0)|v7_waybel_0(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))|~l1_struct_0(esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_22]), c_0_28]), c_0_29]), c_0_27])).
% 0.77/0.97  cnf(c_0_47, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|~v2_struct_0(esk10_1(esk7_1(esk8_0)))|~l1_struct_0(esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_22]), c_0_28]), c_0_29]), c_0_27])).
% 0.77/0.97  fof(c_0_48, plain, ![X21, X22, X23, X24, X25, X29]:(((~r2_hidden(X24,X23)|(~m1_connsp_2(X25,X21,X24)|r1_waybel_0(X21,X22,X25))|~m1_subset_1(X24,u1_struct_0(X21))|X23!=k10_yellow_6(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&((m1_connsp_2(esk2_4(X21,X22,X23,X24),X21,X24)|r2_hidden(X24,X23)|~m1_subset_1(X24,u1_struct_0(X21))|X23!=k10_yellow_6(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r1_waybel_0(X21,X22,esk2_4(X21,X22,X23,X24))|r2_hidden(X24,X23)|~m1_subset_1(X24,u1_struct_0(X21))|X23!=k10_yellow_6(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))))&((m1_subset_1(esk3_3(X21,X22,X23),u1_struct_0(X21))|X23=k10_yellow_6(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(((m1_connsp_2(esk4_3(X21,X22,X23),X21,esk3_3(X21,X22,X23))|~r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k10_yellow_6(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r1_waybel_0(X21,X22,esk4_3(X21,X22,X23))|~r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k10_yellow_6(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r2_hidden(esk3_3(X21,X22,X23),X23)|(~m1_connsp_2(X29,X21,esk3_3(X21,X22,X23))|r1_waybel_0(X21,X22,X29))|X23=k10_yellow_6(X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.77/0.97  fof(c_0_49, plain, ![X37, X38, X39]:(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~v4_orders_2(X38)|~v7_waybel_0(X38)|~l1_waybel_0(X38,X37)|(~m1_subset_1(X39,u1_struct_0(X37))|(~r2_hidden(X39,k10_yellow_6(X37,X38))|r3_waybel_9(X37,X38,X39))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.77/0.97  cnf(c_0_50, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.77/0.97  cnf(c_0_51, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.77/0.97  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.77/0.97  cnf(c_0_53, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|m1_subset_1(k10_yellow_6(esk8_0,esk7_1(esk8_0)),k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_27]), c_0_20]), c_0_21])]), c_0_22]), c_0_28]), c_0_29])).
% 0.77/0.97  cnf(c_0_54, negated_conjecture, (v1_compts_1(esk8_0)|l1_waybel_0(esk10_1(esk7_1(esk8_0)),esk8_0)|v2_struct_0(esk7_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_21])])).
% 0.77/0.97  cnf(c_0_55, negated_conjecture, (v1_compts_1(esk8_0)|v4_orders_2(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_44]), c_0_21])])).
% 0.77/0.97  cnf(c_0_56, negated_conjecture, (v1_compts_1(esk8_0)|v7_waybel_0(esk10_1(esk7_1(esk8_0)))|v2_struct_0(esk7_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_44]), c_0_21])])).
% 0.77/0.97  cnf(c_0_57, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|~v2_struct_0(esk10_1(esk7_1(esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_44]), c_0_21])])).
% 0.77/0.97  cnf(c_0_58, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.77/0.97  fof(c_0_59, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.77/0.97  cnf(c_0_60, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.77/0.97  cnf(c_0_61, plain, (m1_subset_1(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.77/0.97  cnf(c_0_62, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|r1_tarski(k10_yellow_6(esk8_0,esk7_1(esk8_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.77/0.97  cnf(c_0_63, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|m1_subset_1(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_54]), c_0_20]), c_0_21])]), c_0_22]), c_0_55]), c_0_56]), c_0_57])).
% 0.77/0.97  cnf(c_0_64, plain, (X1=k10_yellow_6(X2,X3)|v2_struct_0(X2)|v2_struct_0(X3)|m1_subset_1(esk3_3(X2,X3,X1),u1_struct_0(X2))|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r1_tarski(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_58, c_0_40])).
% 0.77/0.97  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.77/0.97  cnf(c_0_66, plain, (r3_waybel_9(X1,X2,esk1_2(k10_yellow_6(X1,X2),X3))|v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(k10_yellow_6(X1,X2),X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(k10_yellow_6(X1,X2),X3),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_60, c_0_51])).
% 0.77/0.97  cnf(c_0_67, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|m1_subset_1(esk1_2(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1),u1_struct_0(esk8_0))|r1_tarski(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.77/0.97  fof(c_0_68, plain, ![X40, X41, X42, X43]:(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X40)|(~m2_yellow_6(X42,X40,X41)|(~m1_subset_1(X43,u1_struct_0(X40))|(~r3_waybel_9(X40,X42,X43)|r3_waybel_9(X40,X41,X43)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).
% 0.77/0.97  cnf(c_0_69, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_52, c_0_63])).
% 0.77/0.97  cnf(c_0_70, plain, (m1_connsp_2(esk2_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.77/0.97  cnf(c_0_71, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v2_struct_0(X2)|v2_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,k1_xboole_0),u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.77/0.97  fof(c_0_72, plain, ![X18, X19]:(~r2_hidden(X18,X19)|~r1_tarski(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.77/0.97  cnf(c_0_73, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk7_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.97  cnf(c_0_74, negated_conjecture, (v1_compts_1(esk8_0)|r3_waybel_9(esk8_0,esk7_1(esk8_0),esk1_2(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1))|v2_struct_0(esk7_1(esk8_0))|r1_tarski(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_20]), c_0_21])]), c_0_22]), c_0_28]), c_0_29]), c_0_27])).
% 0.77/0.97  cnf(c_0_75, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~r3_waybel_9(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.77/0.97  cnf(c_0_76, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|m1_subset_1(esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1),u1_struct_0(esk8_0))|r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1)), inference(spm,[status(thm)],[c_0_61, c_0_69])).
% 0.77/0.97  cnf(c_0_77, plain, (m1_connsp_2(esk2_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)|v2_struct_0(X2)|v2_struct_0(X1)|r2_hidden(X3,k10_yellow_6(X1,X2))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_70]), c_0_42])).
% 0.77/0.97  cnf(c_0_78, negated_conjecture, (k10_yellow_6(esk8_0,esk7_1(esk8_0))=k1_xboole_0|v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|m1_subset_1(esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_27]), c_0_20]), c_0_21])]), c_0_22]), c_0_28]), c_0_29])).
% 0.77/0.97  cnf(c_0_79, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.77/0.97  cnf(c_0_80, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|r1_tarski(k10_yellow_6(esk8_0,esk7_1(esk8_0)),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_20]), c_0_21])]), c_0_22]), c_0_67])).
% 0.77/0.97  cnf(c_0_81, negated_conjecture, (v1_compts_1(esk8_0)|r3_waybel_9(esk8_0,X1,esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2))|v2_struct_0(esk7_1(esk8_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2)|~r3_waybel_9(esk8_0,X3,esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2))|~m2_yellow_6(X3,esk8_0,X1)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.97  cnf(c_0_82, negated_conjecture, (v1_compts_1(esk8_0)|r3_waybel_9(esk8_0,esk10_1(esk7_1(esk8_0)),esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1))|v2_struct_0(esk7_1(esk8_0))|r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_76]), c_0_20]), c_0_21])]), c_0_22]), c_0_55]), c_0_56]), c_0_54]), c_0_57])).
% 0.77/0.97  cnf(c_0_83, negated_conjecture, (k10_yellow_6(esk8_0,esk7_1(esk8_0))=k1_xboole_0|v1_compts_1(esk8_0)|m1_connsp_2(esk2_4(esk8_0,X1,k10_yellow_6(esk8_0,X1),esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0)),esk8_0,esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0))|v2_struct_0(esk7_1(esk8_0))|v2_struct_0(X1)|r2_hidden(esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0),k10_yellow_6(esk8_0,X1))|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.97  cnf(c_0_84, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|~r2_hidden(X1,k10_yellow_6(esk8_0,esk7_1(esk8_0)))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.77/0.97  cnf(c_0_85, negated_conjecture, (v1_compts_1(esk8_0)|r3_waybel_9(esk8_0,X1,esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2))|v2_struct_0(esk7_1(esk8_0))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X2)|~m2_yellow_6(esk10_1(esk7_1(esk8_0)),esk8_0,X1)|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.77/0.97  cnf(c_0_86, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|r1_waybel_0(X1,X2,X4)|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X4,X1,esk3_3(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.77/0.97  cnf(c_0_87, negated_conjecture, (k10_yellow_6(esk8_0,esk7_1(esk8_0))=k1_xboole_0|v1_compts_1(esk8_0)|m1_connsp_2(esk2_4(esk8_0,esk7_1(esk8_0),k10_yellow_6(esk8_0,esk7_1(esk8_0)),esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0)),esk8_0,esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0))|v2_struct_0(esk7_1(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_27]), c_0_28]), c_0_29]), c_0_84])).
% 0.77/0.97  cnf(c_0_88, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_65])).
% 0.77/0.97  cnf(c_0_89, negated_conjecture, (v1_compts_1(esk8_0)|r3_waybel_9(esk8_0,esk7_1(esk8_0),esk1_2(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1))|v2_struct_0(esk7_1(esk8_0))|r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_34]), c_0_28]), c_0_29]), c_0_27])).
% 0.77/0.97  cnf(c_0_90, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.77/0.97  cnf(c_0_91, negated_conjecture, (k10_yellow_6(esk8_0,esk7_1(esk8_0))=k1_xboole_0|v1_compts_1(esk8_0)|r1_waybel_0(esk8_0,esk7_1(esk8_0),esk2_4(esk8_0,esk7_1(esk8_0),k10_yellow_6(esk8_0,esk7_1(esk8_0)),esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0)))|v2_struct_0(esk7_1(esk8_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_20]), c_0_21])]), c_0_22]), c_0_88]), c_0_28]), c_0_29]), c_0_27])).
% 0.77/0.97  cnf(c_0_92, negated_conjecture, (k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0)))=k1_xboole_0|v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|m1_subset_1(esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_54]), c_0_20]), c_0_21])]), c_0_22]), c_0_55]), c_0_56]), c_0_57])).
% 0.77/0.97  cnf(c_0_93, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|r1_tarski(k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_89]), c_0_20]), c_0_21])]), c_0_22]), c_0_76])).
% 0.77/0.97  cnf(c_0_94, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(X3,k10_yellow_6(X2,X1))|~r1_waybel_0(X2,X1,esk2_4(X2,X1,k10_yellow_6(X2,X1),X3))|~l1_waybel_0(X1,X2)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_90]), c_0_42])).
% 0.77/0.97  cnf(c_0_95, negated_conjecture, (k10_yellow_6(esk8_0,esk7_1(esk8_0))=k1_xboole_0|v1_compts_1(esk8_0)|r1_waybel_0(esk8_0,esk7_1(esk8_0),esk2_4(esk8_0,esk7_1(esk8_0),k10_yellow_6(esk8_0,esk7_1(esk8_0)),esk3_3(esk8_0,esk7_1(esk8_0),k1_xboole_0)))|v2_struct_0(esk7_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_40]), c_0_65])])).
% 0.77/0.97  cnf(c_0_96, negated_conjecture, (k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0)))=k1_xboole_0|v1_compts_1(esk8_0)|m1_connsp_2(esk2_4(esk8_0,X1,k10_yellow_6(esk8_0,X1),esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0)),esk8_0,esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0))|v2_struct_0(esk7_1(esk8_0))|v2_struct_0(X1)|r2_hidden(esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0),k10_yellow_6(esk8_0,X1))|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_92]), c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.97  cnf(c_0_97, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|~r2_hidden(X1,k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))))), inference(spm,[status(thm)],[c_0_79, c_0_93])).
% 0.77/0.97  cnf(c_0_98, negated_conjecture, (k10_yellow_6(esk8_0,esk7_1(esk8_0))=k1_xboole_0|v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_20]), c_0_21])]), c_0_22]), c_0_78]), c_0_28]), c_0_29]), c_0_27]), c_0_84])).
% 0.77/0.97  cnf(c_0_99, negated_conjecture, (k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0)))=k1_xboole_0|v1_compts_1(esk8_0)|m1_connsp_2(esk2_4(esk8_0,esk10_1(esk7_1(esk8_0)),k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0)),esk8_0,esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0))|v2_struct_0(esk7_1(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_54]), c_0_55]), c_0_56]), c_0_97]), c_0_57])).
% 0.77/0.97  cnf(c_0_100, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_53, c_0_98])).
% 0.77/0.97  fof(c_0_101, plain, ![X35, X36]:((~v3_yellow_6(X36,X35)|k10_yellow_6(X35,X36)!=k1_xboole_0|(v2_struct_0(X36)|~v4_orders_2(X36)|~v7_waybel_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(k10_yellow_6(X35,X36)=k1_xboole_0|v3_yellow_6(X36,X35)|(v2_struct_0(X36)|~v4_orders_2(X36)|~v7_waybel_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.77/0.97  cnf(c_0_102, negated_conjecture, (k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0)))=k1_xboole_0|v1_compts_1(esk8_0)|r1_waybel_0(esk8_0,esk10_1(esk7_1(esk8_0)),esk2_4(esk8_0,esk10_1(esk7_1(esk8_0)),k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0))),esk3_3(esk8_0,esk10_1(esk7_1(esk8_0)),k1_xboole_0)))|v2_struct_0(esk7_1(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_99]), c_0_20]), c_0_21])]), c_0_22]), c_0_88]), c_0_100]), c_0_55]), c_0_56]), c_0_54]), c_0_57])).
% 0.77/0.97  cnf(c_0_103, negated_conjecture, (k10_yellow_6(esk8_0,X1)=k1_xboole_0|v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))|v2_struct_0(X1)|m1_subset_1(esk3_3(esk8_0,X1,k1_xboole_0),u1_struct_0(esk8_0))|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_100]), c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.97  cnf(c_0_104, negated_conjecture, (v3_yellow_6(esk10_1(X1),esk8_0)|v2_struct_0(X1)|v1_compts_1(esk8_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.97  cnf(c_0_105, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.77/0.97  cnf(c_0_106, negated_conjecture, (k10_yellow_6(esk8_0,esk10_1(esk7_1(esk8_0)))=k1_xboole_0|v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_102]), c_0_20]), c_0_21])]), c_0_22]), c_0_103]), c_0_55]), c_0_56]), c_0_54]), c_0_97]), c_0_57])).
% 0.77/0.97  cnf(c_0_107, negated_conjecture, (v1_compts_1(esk8_0)|v3_yellow_6(esk10_1(esk7_1(esk8_0)),esk8_0)|v2_struct_0(esk7_1(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_27]), c_0_28]), c_0_29])).
% 0.77/0.97  cnf(c_0_108, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk7_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.97  cnf(c_0_109, negated_conjecture, (v1_compts_1(esk8_0)|v2_struct_0(esk7_1(esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_20]), c_0_21])]), c_0_22]), c_0_55]), c_0_56]), c_0_54]), c_0_107]), c_0_57])).
% 0.77/0.97  fof(c_0_110, plain, ![X48, X49]:((m1_subset_1(esk6_2(X48,X49),u1_struct_0(X48))|(v2_struct_0(X49)|~v4_orders_2(X49)|~v7_waybel_0(X49)|~l1_waybel_0(X49,X48))|~v1_compts_1(X48)|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(r3_waybel_9(X48,X49,esk6_2(X48,X49))|(v2_struct_0(X49)|~v4_orders_2(X49)|~v7_waybel_0(X49)|~l1_waybel_0(X49,X48))|~v1_compts_1(X48)|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).
% 0.77/0.97  cnf(c_0_111, negated_conjecture, (l1_waybel_0(esk9_0,esk8_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.97  cnf(c_0_112, negated_conjecture, (v1_compts_1(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.97  cnf(c_0_113, negated_conjecture, (v7_waybel_0(esk9_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.97  cnf(c_0_114, negated_conjecture, (v4_orders_2(esk9_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.97  cnf(c_0_115, negated_conjecture, (~v2_struct_0(esk9_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.97  fof(c_0_116, plain, ![X44, X45, X46]:((m2_yellow_6(esk5_3(X44,X45,X46),X44,X45)|~r3_waybel_9(X44,X45,X46)|~m1_subset_1(X46,u1_struct_0(X44))|(v2_struct_0(X45)|~v4_orders_2(X45)|~v7_waybel_0(X45)|~l1_waybel_0(X45,X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))&(r2_hidden(X46,k10_yellow_6(X44,esk5_3(X44,X45,X46)))|~r3_waybel_9(X44,X45,X46)|~m1_subset_1(X46,u1_struct_0(X44))|(v2_struct_0(X45)|~v4_orders_2(X45)|~v7_waybel_0(X45)|~l1_waybel_0(X45,X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.77/0.97  cnf(c_0_117, plain, (m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.77/0.97  cnf(c_0_118, negated_conjecture, (l1_waybel_0(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_112])])).
% 0.77/0.97  cnf(c_0_119, negated_conjecture, (v7_waybel_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_112])])).
% 0.77/0.97  cnf(c_0_120, negated_conjecture, (v4_orders_2(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_112])])).
% 0.77/0.97  cnf(c_0_121, negated_conjecture, (~v2_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_112])])).
% 0.77/0.97  cnf(c_0_122, plain, (m2_yellow_6(esk5_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.77/0.97  cnf(c_0_123, negated_conjecture, (m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_112]), c_0_119]), c_0_120]), c_0_20]), c_0_21])]), c_0_121]), c_0_22])).
% 0.77/0.98  cnf(c_0_124, plain, (r3_waybel_9(X1,X2,esk6_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.77/0.98  cnf(c_0_125, negated_conjecture, (m2_yellow_6(esk5_3(esk8_0,X1,esk6_2(esk8_0,esk9_0)),esk8_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.98  cnf(c_0_126, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_118]), c_0_112]), c_0_119]), c_0_120]), c_0_20]), c_0_21])]), c_0_121]), c_0_22])).
% 0.77/0.98  cnf(c_0_127, negated_conjecture, (m2_yellow_6(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)),esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_118]), c_0_119]), c_0_120])]), c_0_121])).
% 0.77/0.98  cnf(c_0_128, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.77/0.98  cnf(c_0_129, negated_conjecture, (l1_waybel_0(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)),esk8_0)|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_127]), c_0_118]), c_0_119]), c_0_120])]), c_0_121]), c_0_22])).
% 0.77/0.98  cnf(c_0_130, negated_conjecture, (v4_orders_2(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_127]), c_0_118]), c_0_119]), c_0_120])]), c_0_121]), c_0_22])).
% 0.77/0.98  cnf(c_0_131, negated_conjecture, (v7_waybel_0(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_127]), c_0_118]), c_0_119]), c_0_120])]), c_0_121]), c_0_22])).
% 0.77/0.98  cnf(c_0_132, negated_conjecture, (~v2_struct_0(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))|~l1_struct_0(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_127]), c_0_118]), c_0_119]), c_0_120])]), c_0_121]), c_0_22])).
% 0.77/0.98  cnf(c_0_133, plain, (r2_hidden(X1,k10_yellow_6(X2,esk5_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.77/0.98  cnf(c_0_134, negated_conjecture, (~m2_yellow_6(X1,esk8_0,esk9_0)|~v3_yellow_6(X1,esk8_0)|~v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.98  cnf(c_0_135, negated_conjecture, (k10_yellow_6(esk8_0,esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))=k1_xboole_0|v3_yellow_6(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)),esk8_0)|~l1_struct_0(esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_20]), c_0_21])]), c_0_22]), c_0_130]), c_0_131]), c_0_132])).
% 0.77/0.98  cnf(c_0_136, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk6_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk5_3(esk8_0,X1,esk6_2(esk8_0,esk9_0))))|~r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))|~l1_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_123]), c_0_20]), c_0_21])]), c_0_22])).
% 0.77/0.98  cnf(c_0_137, negated_conjecture, (~v3_yellow_6(X1,esk8_0)|~m2_yellow_6(X1,esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_112])])).
% 0.77/0.98  cnf(c_0_138, negated_conjecture, (k10_yellow_6(esk8_0,esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))=k1_xboole_0|v3_yellow_6(esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_44]), c_0_21])])).
% 0.77/0.98  cnf(c_0_139, negated_conjecture, (r2_hidden(esk6_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_126]), c_0_118]), c_0_119]), c_0_120])]), c_0_121])).
% 0.77/0.98  cnf(c_0_140, negated_conjecture, (k10_yellow_6(esk8_0,esk5_3(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_127])])).
% 0.77/0.98  cnf(c_0_141, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_140]), c_0_88]), ['proof']).
% 0.77/0.98  # SZS output end CNFRefutation
% 0.77/0.98  # Proof object total steps             : 142
% 0.77/0.98  # Proof object clause steps            : 109
% 0.77/0.98  # Proof object formula steps           : 33
% 0.77/0.98  # Proof object conjectures             : 75
% 0.77/0.98  # Proof object clause conjectures      : 72
% 0.77/0.98  # Proof object formula conjectures     : 3
% 0.77/0.98  # Proof object initial clauses used    : 39
% 0.77/0.98  # Proof object initial formulas used   : 16
% 0.77/0.98  # Proof object generating inferences   : 62
% 0.77/0.98  # Proof object simplifying inferences  : 251
% 0.77/0.98  # Training examples: 0 positive, 0 negative
% 0.77/0.98  # Parsed axioms                        : 16
% 0.77/0.98  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.98  # Initial clauses                      : 45
% 0.77/0.98  # Removed in clause preprocessing      : 0
% 0.77/0.98  # Initial clauses in saturation        : 45
% 0.77/0.98  # Processed clauses                    : 1765
% 0.77/0.98  # ...of these trivial                  : 0
% 0.77/0.98  # ...subsumed                          : 451
% 0.77/0.98  # ...remaining for further processing  : 1314
% 0.77/0.98  # Other redundant clauses eliminated   : 3
% 0.77/0.98  # Clauses deleted for lack of memory   : 0
% 0.77/0.98  # Backward-subsumed                    : 1002
% 0.77/0.98  # Backward-rewritten                   : 24
% 0.77/0.98  # Generated clauses                    : 6067
% 0.77/0.98  # ...of the previous two non-trivial   : 5960
% 0.77/0.98  # Contextual simplify-reflections      : 1531
% 0.77/0.98  # Paramodulations                      : 6064
% 0.77/0.98  # Factorizations                       : 0
% 0.77/0.98  # Equation resolutions                 : 3
% 0.77/0.98  # Propositional unsat checks           : 0
% 0.77/0.98  #    Propositional check models        : 0
% 0.77/0.98  #    Propositional check unsatisfiable : 0
% 0.77/0.98  #    Propositional clauses             : 0
% 0.77/0.98  #    Propositional clauses after purity: 0
% 0.77/0.98  #    Propositional unsat core size     : 0
% 0.77/0.98  #    Propositional preprocessing time  : 0.000
% 0.77/0.98  #    Propositional encoding time       : 0.000
% 0.77/0.98  #    Propositional solver time         : 0.000
% 0.77/0.98  #    Success case prop preproc time    : 0.000
% 0.77/0.98  #    Success case prop encoding time   : 0.000
% 0.77/0.98  #    Success case prop solver time     : 0.000
% 0.77/0.98  # Current number of processed clauses  : 240
% 0.77/0.98  #    Positive orientable unit clauses  : 14
% 0.77/0.98  #    Positive unorientable unit clauses: 0
% 0.77/0.98  #    Negative unit clauses             : 7
% 0.77/0.98  #    Non-unit-clauses                  : 219
% 0.77/0.98  # Current number of unprocessed clauses: 4201
% 0.77/0.98  # ...number of literals in the above   : 33484
% 0.77/0.98  # Current number of archived formulas  : 0
% 0.77/0.98  # Current number of archived clauses   : 1071
% 0.77/0.98  # Clause-clause subsumption calls (NU) : 814404
% 0.77/0.98  # Rec. Clause-clause subsumption calls : 18880
% 0.77/0.98  # Non-unit clause-clause subsumptions  : 2977
% 0.77/0.98  # Unit Clause-clause subsumption calls : 308
% 0.77/0.98  # Rewrite failures with RHS unbound    : 0
% 0.77/0.98  # BW rewrite match attempts            : 7
% 0.77/0.98  # BW rewrite match successes           : 2
% 0.77/0.98  # Condensation attempts                : 0
% 0.77/0.98  # Condensation successes               : 0
% 0.77/0.98  # Termbank termtop insertions          : 522767
% 0.77/0.98  
% 0.77/0.98  # -------------------------------------------------
% 0.77/0.98  # User time                : 0.623 s
% 0.77/0.98  # System time              : 0.007 s
% 0.77/0.98  # Total time               : 0.630 s
% 0.77/0.98  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
