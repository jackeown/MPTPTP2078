%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2077+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:12 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 492 expanded)
%              Number of clauses        :   78 ( 168 expanded)
%              Number of leaves         :   16 ( 125 expanded)
%              Depth                    :   17
%              Number of atoms          :  728 (5403 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   44 (   6 average)
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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

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

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

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

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

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
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ v4_orders_2(X16)
      | ~ v7_waybel_0(X16)
      | ~ l1_waybel_0(X16,X15)
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | ~ r2_hidden(X17,k10_yellow_6(X15,X16))
      | r3_waybel_9(X15,X16,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X18,X19)
      | v1_xboole_0(X19)
      | r2_hidden(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_19,plain,(
    ! [X20,X21,X22,X23] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | v2_struct_0(X21)
      | ~ v4_orders_2(X21)
      | ~ v7_waybel_0(X21)
      | ~ l1_waybel_0(X21,X20)
      | ~ m2_yellow_6(X22,X20,X21)
      | ~ m1_subset_1(X23,u1_struct_0(X20))
      | ~ r3_waybel_9(X20,X22,X23)
      | r3_waybel_9(X20,X21,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_waybel_9])])])])).

fof(c_0_20,negated_conjecture,(
    ! [X42,X43] :
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
      & ( ~ m2_yellow_6(X42,esk5_0,esk6_0)
        | ~ v3_yellow_6(X42,esk5_0)
        | ~ v1_compts_1(esk5_0) )
      & ( m2_yellow_6(esk7_1(X43),esk5_0,X43)
        | v2_struct_0(X43)
        | ~ v4_orders_2(X43)
        | ~ v7_waybel_0(X43)
        | ~ l1_waybel_0(X43,esk5_0)
        | v1_compts_1(esk5_0) )
      & ( v3_yellow_6(esk7_1(X43),esk5_0)
        | v2_struct_0(X43)
        | ~ v4_orders_2(X43)
        | ~ v7_waybel_0(X43)
        | ~ l1_waybel_0(X43,esk5_0)
        | v1_compts_1(esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X13] : m1_subset_1(esk1_1(X13),X13) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_24,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | m1_subset_1(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_25,plain,(
    ! [X7,X8] :
      ( v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ v4_orders_2(X8)
      | ~ v7_waybel_0(X8)
      | ~ l1_waybel_0(X8,X7)
      | m1_subset_1(k10_yellow_6(X7,X8),k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_26,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m2_yellow_6(esk7_1(X1),esk5_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk5_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v1_xboole_0(k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,k10_yellow_6(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X28,X29,X32] :
      ( ( m1_subset_1(esk3_2(X28,X29),u1_struct_0(X28))
        | v2_struct_0(X29)
        | ~ v4_orders_2(X29)
        | ~ v7_waybel_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | ~ v1_compts_1(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( r3_waybel_9(X28,X29,esk3_2(X28,X29))
        | v2_struct_0(X29)
        | ~ v4_orders_2(X29)
        | ~ v7_waybel_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | ~ v1_compts_1(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ v2_struct_0(esk4_1(X28))
        | v1_compts_1(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v4_orders_2(esk4_1(X28))
        | v1_compts_1(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v7_waybel_0(esk4_1(X28))
        | v1_compts_1(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( l1_waybel_0(esk4_1(X28),X28)
        | v1_compts_1(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X28))
        | ~ r3_waybel_9(X28,esk4_1(X28),X32)
        | v1_compts_1(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | r3_waybel_9(esk5_0,X1,X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk5_0,esk7_1(X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_37,plain,
    ( r3_waybel_9(X1,X2,esk1_1(k10_yellow_6(X1,X2)))
    | v1_xboole_0(k10_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(esk1_1(k10_yellow_6(X1,X2)),u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k10_yellow_6(X2,X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v2_struct_0(X12)
        | ~ m2_yellow_6(X12,X10,X11)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ l1_waybel_0(X11,X10) )
      & ( v4_orders_2(X12)
        | ~ m2_yellow_6(X12,X10,X11)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ l1_waybel_0(X11,X10) )
      & ( v7_waybel_0(X12)
        | ~ m2_yellow_6(X12,X10,X11)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ l1_waybel_0(X11,X10) )
      & ( l1_waybel_0(X12,X10)
        | ~ m2_yellow_6(X12,X10,X11)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v2_struct_0(X11)
        | ~ v4_orders_2(X11)
        | ~ v7_waybel_0(X11)
        | ~ l1_waybel_0(X11,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_40,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk4_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | r3_waybel_9(esk5_0,X1,esk1_1(k10_yellow_6(esk5_0,esk7_1(X1))))
    | v1_xboole_0(k10_yellow_6(esk5_0,esk7_1(X1)))
    | v2_struct_0(esk7_1(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk1_1(k10_yellow_6(esk5_0,esk7_1(X1))),u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk7_1(X1),esk5_0)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(esk7_1(X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk7_1(X1))
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k10_yellow_6(X1,X2))
    | m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k10_yellow_6(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_43,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_44,plain,(
    ! [X39] :
      ( ~ v1_xboole_0(X39)
      | X39 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_45,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))))
    | v2_struct_0(esk7_1(esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ m1_subset_1(esk1_1(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0)))),u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk7_1(esk4_1(esk5_0)),esk5_0)
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0)
    | ~ v7_waybel_0(esk7_1(esk4_1(esk5_0)))
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk7_1(esk4_1(esk5_0)))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k10_yellow_6(X1,X2))
    | m1_subset_1(esk1_1(k10_yellow_6(X1,X2)),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v4_orders_2(esk7_1(X1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27]),c_0_30])).

cnf(c_0_48,plain,
    ( l1_waybel_0(esk4_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_49,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | ~ v1_xboole_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_50,plain,(
    ! [X24,X25,X26] :
      ( ( m2_yellow_6(esk2_3(X24,X25,X26),X24,X25)
        | ~ r3_waybel_9(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(X26,k10_yellow_6(X24,esk2_3(X24,X25,X26)))
        | ~ r3_waybel_9(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

fof(c_0_51,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_52,plain,(
    ! [X5,X6] :
      ( ( ~ v3_yellow_6(X6,X5)
        | k10_yellow_6(X5,X6) != k1_xboole_0
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( k10_yellow_6(X5,X6) = k1_xboole_0
        | v3_yellow_6(X6,X5)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v1_xboole_0(k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))))
    | v2_struct_0(esk7_1(esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ l1_waybel_0(esk7_1(esk4_1(esk5_0)),esk5_0)
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0)
    | ~ v7_waybel_0(esk7_1(esk4_1(esk5_0)))
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk7_1(esk4_1(esk5_0)))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_55,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk4_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v4_orders_2(esk7_1(esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ l1_struct_0(esk5_0)
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_61,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_62,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k10_yellow_6(esk5_0,esk7_1(esk4_1(esk5_0))) = k1_xboole_0
    | v1_compts_1(esk5_0)
    | v2_struct_0(esk7_1(esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ l1_waybel_0(esk7_1(esk4_1(esk5_0)),esk5_0)
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0)
    | ~ v7_waybel_0(esk7_1(esk4_1(esk5_0)))
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk7_1(esk4_1(esk5_0)))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( v3_yellow_6(esk7_1(X1),esk5_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk5_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v4_orders_2(esk7_1(esk4_1(esk5_0)))
    | ~ l1_struct_0(esk5_0)
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_67,plain,
    ( v7_waybel_0(esk4_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,esk1_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_32])).

cnf(c_0_69,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk5_0,esk6_0)
    | ~ v3_yellow_6(X1,esk5_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( v4_orders_2(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_71,negated_conjecture,
    ( v7_waybel_0(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_75,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_76,plain,
    ( v4_orders_2(esk2_3(X1,X2,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_58]),c_0_59])).

cnf(c_0_77,plain,
    ( v7_waybel_0(esk2_3(X1,X2,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_58]),c_0_59])).

cnf(c_0_78,plain,
    ( l1_waybel_0(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_58]),c_0_59])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X1,X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_struct_0(esk2_3(X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_58]),c_0_59])).

cnf(c_0_80,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk7_1(esk4_1(esk5_0)))
    | v2_struct_0(esk4_1(esk5_0))
    | ~ l1_waybel_0(esk7_1(esk4_1(esk5_0)),esk5_0)
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0)
    | ~ v7_waybel_0(esk7_1(esk4_1(esk5_0)))
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk7_1(esk4_1(esk5_0)))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_28]),c_0_29])]),c_0_30]),c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | l1_waybel_0(esk7_1(X1),esk5_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_27]),c_0_30])).

cnf(c_0_82,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v4_orders_2(esk7_1(esk4_1(esk5_0)))
    | ~ l1_struct_0(esk5_0)
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_83,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v7_waybel_0(esk7_1(X1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_27]),c_0_30])).

cnf(c_0_84,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_struct_0(esk7_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_27]),c_0_30])).

cnf(c_0_85,plain,
    ( v1_xboole_0(esk1_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,esk1_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_22])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_compts_1(esk5_0)
    | ~ r3_waybel_9(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v3_yellow_6(esk2_3(esk5_0,esk6_0,X1),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_58]),c_0_28]),c_0_29])]),c_0_30]),c_0_70]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k1_xboole_0)
    | v3_yellow_6(esk2_3(X2,X3,X1),X2)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77]),c_0_78]),c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | ~ l1_struct_0(esk5_0)
    | ~ l1_waybel_0(esk4_1(esk5_0),esk5_0)
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_83]),c_0_84])).

cnf(c_0_89,plain,
    ( v1_xboole_0(esk1_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_32])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v1_compts_1(esk5_0)
    | ~ r3_waybel_9(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_28]),c_0_29])]),c_0_30]),c_0_70]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_91,plain,
    ( r3_waybel_9(X1,X2,esk3_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_92,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_struct_0(esk4_1(esk5_0))
    | ~ l1_struct_0(esk5_0)
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_48]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_93,plain,
    ( esk1_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),k1_xboole_0)
    | ~ v1_compts_1(esk5_0)
    | ~ m1_subset_1(esk3_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_28]),c_0_29])]),c_0_30]),c_0_70]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_95,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_96,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ v7_waybel_0(esk4_1(esk5_0))
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_92]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),k1_xboole_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_28]),c_0_29])]),c_0_30]),c_0_70]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_99,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ v4_orders_2(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_67]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_100,plain,
    ( v4_orders_2(esk4_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_compts_1(esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_103,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_104,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_106,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_59]),c_0_28])])).

cnf(c_0_108,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_106,c_0_107]),
    [proof]).

%------------------------------------------------------------------------------
