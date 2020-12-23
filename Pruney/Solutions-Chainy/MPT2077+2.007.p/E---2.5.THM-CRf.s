%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:06 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  137 (4431 expanded)
%              Number of clauses        :  104 (1431 expanded)
%              Number of leaves         :   16 (1159 expanded)
%              Depth                    :   36
%              Number of atoms          : 1216 (51740 expanded)
%              Number of equality atoms :   49 ( 222 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal clause size      :   81 (   8 average)
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ r1_tarski(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_18,plain,(
    ! [X48,X49,X50] :
      ( ( m2_yellow_6(esk6_3(X48,X49,X50),X48,X49)
        | ~ r3_waybel_9(X48,X49,X50)
        | ~ m1_subset_1(X50,u1_struct_0(X48))
        | v2_struct_0(X49)
        | ~ v4_orders_2(X49)
        | ~ v7_waybel_0(X49)
        | ~ l1_waybel_0(X49,X48)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( r2_hidden(X50,k10_yellow_6(X48,esk6_3(X48,X49,X50)))
        | ~ r3_waybel_9(X48,X49,X50)
        | ~ m1_subset_1(X50,u1_struct_0(X48))
        | v2_struct_0(X49)
        | ~ v4_orders_2(X49)
        | ~ v7_waybel_0(X49)
        | ~ l1_waybel_0(X49,X48)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).

fof(c_0_19,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v2_struct_0(X33)
        | ~ m2_yellow_6(X33,X31,X32)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31) )
      & ( v4_orders_2(X33)
        | ~ m2_yellow_6(X33,X31,X32)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31) )
      & ( v7_waybel_0(X33)
        | ~ m2_yellow_6(X33,X31,X32)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31) )
      & ( l1_waybel_0(X33,X31)
        | ~ m2_yellow_6(X33,X31,X32)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31)
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

fof(c_0_20,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_21,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | m1_subset_1(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_22,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | v2_struct_0(X30)
      | ~ v4_orders_2(X30)
      | ~ v7_waybel_0(X30)
      | ~ l1_waybel_0(X30,X29)
      | m1_subset_1(k10_yellow_6(X29,X30),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

fof(c_0_23,negated_conjecture,(
    ! [X59,X60] :
      ( ~ v2_struct_0(esk9_0)
      & v2_pre_topc(esk9_0)
      & l1_pre_topc(esk9_0)
      & ( ~ v2_struct_0(esk10_0)
        | ~ v1_compts_1(esk9_0) )
      & ( v4_orders_2(esk10_0)
        | ~ v1_compts_1(esk9_0) )
      & ( v7_waybel_0(esk10_0)
        | ~ v1_compts_1(esk9_0) )
      & ( l1_waybel_0(esk10_0,esk9_0)
        | ~ v1_compts_1(esk9_0) )
      & ( ~ m2_yellow_6(X59,esk9_0,esk10_0)
        | ~ v3_yellow_6(X59,esk9_0)
        | ~ v1_compts_1(esk9_0) )
      & ( m2_yellow_6(esk11_1(X60),esk9_0,X60)
        | v2_struct_0(X60)
        | ~ v4_orders_2(X60)
        | ~ v7_waybel_0(X60)
        | ~ l1_waybel_0(X60,esk9_0)
        | v1_compts_1(esk9_0) )
      & ( v3_yellow_6(esk11_1(X60),esk9_0)
        | v2_struct_0(X60)
        | ~ v4_orders_2(X60)
        | ~ v7_waybel_0(X60)
        | ~ l1_waybel_0(X60,esk9_0)
        | v1_compts_1(esk9_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,esk6_3(X2,X3,X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X38,X39] :
      ( ( ~ v3_yellow_6(X39,X38)
        | k10_yellow_6(X38,X39) != k1_xboole_0
        | v2_struct_0(X39)
        | ~ v4_orders_2(X39)
        | ~ v7_waybel_0(X39)
        | ~ l1_waybel_0(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( k10_yellow_6(X38,X39) = k1_xboole_0
        | v3_yellow_6(X39,X38)
        | v2_struct_0(X39)
        | ~ v4_orders_2(X39)
        | ~ v7_waybel_0(X39)
        | ~ l1_waybel_0(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).

fof(c_0_27,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_28,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( m2_yellow_6(esk6_3(X1,X2,X3),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_34,plain,(
    ! [X40,X41,X42,X43] :
      ( ( ~ r3_waybel_9(X40,X41,X42)
        | ~ m1_connsp_2(X43,X40,X42)
        | r2_waybel_0(X40,X41,X43)
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | v2_struct_0(X41)
        | ~ l1_waybel_0(X41,X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_connsp_2(esk5_3(X40,X41,X42),X40,X42)
        | r3_waybel_9(X40,X41,X42)
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | v2_struct_0(X41)
        | ~ l1_waybel_0(X41,X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ r2_waybel_0(X40,X41,esk5_3(X40,X41,X42))
        | r3_waybel_9(X40,X41,X42)
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | v2_struct_0(X41)
        | ~ l1_waybel_0(X41,X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).

fof(c_0_35,plain,(
    ! [X45,X46,X47] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | v2_struct_0(X46)
      | ~ v4_orders_2(X46)
      | ~ v7_waybel_0(X46)
      | ~ l1_waybel_0(X46,X45)
      | ~ m1_subset_1(X47,u1_struct_0(X45))
      | ~ r2_hidden(X47,k10_yellow_6(X45,X46))
      | r3_waybel_9(X45,X46,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( ~ m2_yellow_6(X1,esk9_0,esk10_0)
    | ~ v3_yellow_6(X1,esk9_0)
    | ~ v1_compts_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( v4_orders_2(esk10_0)
    | ~ v1_compts_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( v7_waybel_0(esk10_0)
    | ~ v1_compts_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( l1_waybel_0(esk10_0,esk9_0)
    | ~ v1_compts_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk10_0)
    | ~ v1_compts_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(k10_yellow_6(X1,esk6_3(X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_47,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v3_yellow_6(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_49,plain,
    ( v4_orders_2(esk6_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_50,plain,
    ( v7_waybel_0(esk6_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_30])).

cnf(c_0_51,plain,
    ( l1_waybel_0(esk6_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_30])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_struct_0(esk6_3(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_30])).

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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,k10_yellow_6(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_56,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_compts_1(esk9_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v3_yellow_6(esk6_3(esk9_0,esk10_0,X1),esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_39]),c_0_40])]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_58,plain,
    ( v3_yellow_6(esk6_3(X1,X2,X3),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

fof(c_0_59,plain,(
    ! [X52,X53,X56] :
      ( ( m1_subset_1(esk7_2(X52,X53),u1_struct_0(X52))
        | v2_struct_0(X53)
        | ~ v4_orders_2(X53)
        | ~ v7_waybel_0(X53)
        | ~ l1_waybel_0(X53,X52)
        | ~ v1_compts_1(X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( r3_waybel_9(X52,X53,esk7_2(X52,X53))
        | v2_struct_0(X53)
        | ~ v4_orders_2(X53)
        | ~ v7_waybel_0(X53)
        | ~ l1_waybel_0(X53,X52)
        | ~ v1_compts_1(X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( ~ v2_struct_0(esk8_1(X52))
        | v1_compts_1(X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( v4_orders_2(esk8_1(X52))
        | v1_compts_1(X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( v7_waybel_0(esk8_1(X52))
        | v1_compts_1(X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( l1_waybel_0(esk8_1(X52),X52)
        | v1_compts_1(X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) )
      & ( ~ m1_subset_1(X56,u1_struct_0(X52))
        | ~ r3_waybel_9(X52,esk8_1(X52),X56)
        | v1_compts_1(X52)
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).

fof(c_0_60,plain,(
    ! [X34,X35,X36,X37] :
      ( v2_struct_0(X34)
      | ~ l1_struct_0(X34)
      | v2_struct_0(X35)
      | ~ v4_orders_2(X35)
      | ~ v7_waybel_0(X35)
      | ~ l1_waybel_0(X35,X34)
      | ~ m2_yellow_6(X36,X34,X35)
      | ~ r2_waybel_0(X34,X36,X37)
      | r2_waybel_0(X34,X35,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

cnf(c_0_61,plain,
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
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_62,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_compts_1(esk9_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_39]),c_0_40])]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_64,plain,
    ( r3_waybel_9(X1,X2,esk7_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_65,plain,(
    ! [X20,X21,X22,X23,X24,X28] :
      ( ( ~ r2_hidden(X23,X22)
        | ~ m1_connsp_2(X24,X20,X23)
        | r1_waybel_0(X20,X21,X24)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | X22 != k10_yellow_6(X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_connsp_2(esk2_4(X20,X21,X22,X23),X20,X23)
        | r2_hidden(X23,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | X22 != k10_yellow_6(X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r1_waybel_0(X20,X21,esk2_4(X20,X21,X22,X23))
        | r2_hidden(X23,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | X22 != k10_yellow_6(X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk3_3(X20,X21,X22),u1_struct_0(X20))
        | X22 = k10_yellow_6(X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_connsp_2(esk4_3(X20,X21,X22),X20,esk3_3(X20,X21,X22))
        | ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k10_yellow_6(X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r1_waybel_0(X20,X21,esk4_3(X20,X21,X22))
        | ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k10_yellow_6(X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X22)
        | ~ m1_connsp_2(X28,X20,esk3_3(X20,X21,X22))
        | r1_waybel_0(X20,X21,X28)
        | X22 = k10_yellow_6(X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( m2_yellow_6(esk11_1(X1),esk9_0,X1)
    | v2_struct_0(X1)
    | v1_compts_1(esk9_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_68,plain,
    ( r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(X1,X2),X4)
    | ~ m1_connsp_2(X3,X1,esk1_2(k10_yellow_6(X1,X2),X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( m1_connsp_2(esk5_3(X1,X2,X3),X1,X3)
    | r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk1_2(k10_yellow_6(X2,X1),X3),u1_struct_0(X2))
    | r1_tarski(k10_yellow_6(X2,X1),X3)
    | ~ l1_waybel_0(X1,X2)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_compts_1(esk9_0)
    | ~ m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_39]),c_0_40])]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_72,plain,
    ( m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( v1_compts_1(esk9_0)
    | r2_waybel_0(esk9_0,X1,X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(esk9_0,esk11_1(X1),X2)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_41])).

cnf(c_0_77,plain,
    ( r3_waybel_9(X1,X2,esk1_2(k10_yellow_6(X1,X3),X4))
    | r2_waybel_0(X1,X3,esk5_3(X1,X2,esk1_2(k10_yellow_6(X1,X3),X4)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tarski(k10_yellow_6(X1,X3),X4)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_compts_1(esk9_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_39]),c_0_40])]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_79,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_80,plain,
    ( X1 = k10_yellow_6(X2,X3)
    | r1_waybel_0(X2,X3,esk2_4(X2,X4,X5,esk3_3(X2,X3,X1)))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_hidden(esk3_3(X2,X3,X1),X5)
    | r2_hidden(esk3_3(X2,X3,X1),X1)
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
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

fof(c_0_81,plain,(
    ! [X13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_82,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_83,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,esk5_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_84,negated_conjecture,
    ( r3_waybel_9(esk9_0,X1,esk1_2(k10_yellow_6(esk9_0,esk11_1(X2)),X3))
    | r2_waybel_0(esk9_0,X2,esk5_3(esk9_0,X1,esk1_2(k10_yellow_6(esk9_0,esk11_1(X2)),X3)))
    | v2_struct_0(esk11_1(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tarski(k10_yellow_6(esk9_0,esk11_1(X2)),X3)
    | ~ l1_waybel_0(esk11_1(X2),esk9_0)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk11_1(X2))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(esk11_1(X2))
    | ~ v4_orders_2(X2)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_85,plain,
    ( X1 = k10_yellow_6(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_hidden(esk3_3(X2,X3,X1),X1)
    | r2_hidden(esk3_3(X2,X3,X1),X4)
    | X4 != k10_yellow_6(X2,X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_75])).

cnf(c_0_86,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_48])).

cnf(c_0_88,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk8_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_89,negated_conjecture,
    ( r3_waybel_9(esk9_0,X1,esk1_2(k10_yellow_6(esk9_0,esk11_1(X1)),X2))
    | v2_struct_0(esk11_1(X1))
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(esk9_0,esk11_1(X1)),X2)
    | ~ l1_waybel_0(esk11_1(X1),esk9_0)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk11_1(X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk11_1(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0)
    | ~ m1_subset_1(esk1_2(k10_yellow_6(esk9_0,esk11_1(X1)),X2),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_90,plain,
    ( X1 = k10_yellow_6(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | r2_hidden(esk3_3(X2,X3,X1),X1)
    | k10_yellow_6(X2,X3) != k1_xboole_0
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | r1_tarski(k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))),X1)
    | ~ l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0)
    | ~ m1_subset_1(esk1_2(k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))),X1),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_92,plain,
    ( X1 = k10_yellow_6(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k10_yellow_6(X2,X3) != k1_xboole_0
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,esk3_3(X2,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | r1_tarski(k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))),X1)
    | ~ l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_70]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_94,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k10_yellow_6(X1,X2)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k10_yellow_6(X1,X2) != k1_xboole_0
    | ~ l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_struct_0(esk9_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_95,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k10_yellow_6(esk9_0,X1)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | k10_yellow_6(esk9_0,X1) != k1_xboole_0
    | ~ l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_37]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_96,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_47]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_97,negated_conjecture,
    ( v1_compts_1(esk9_0)
    | l1_waybel_0(esk11_1(X1),esk9_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_67]),c_0_41])).

cnf(c_0_98,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_78])).

cnf(c_0_99,plain,
    ( l1_waybel_0(esk8_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_100,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_101,negated_conjecture,
    ( v1_compts_1(esk9_0)
    | v7_waybel_0(esk11_1(X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_67]),c_0_41])).

cnf(c_0_102,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_78])).

cnf(c_0_103,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_99]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_104,negated_conjecture,
    ( v1_compts_1(esk9_0)
    | v4_orders_2(esk11_1(X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_67]),c_0_41])).

cnf(c_0_105,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_78])).

cnf(c_0_106,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_99]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_107,plain,
    ( v7_waybel_0(esk8_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_108,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_109,plain,
    ( v4_orders_2(esk8_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_110,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_111,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(X1,esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_30]),c_0_40])])).

cnf(c_0_112,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_yellow_6(X1,X2)
    | k10_yellow_6(X2,X1) != k1_xboole_0
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_113,negated_conjecture,
    ( k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))) = k1_xboole_0
    | v3_yellow_6(esk8_1(esk9_0),esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk8_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_99]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_114,plain,
    ( X1 = k10_yellow_6(X2,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | r2_hidden(esk3_3(X2,X3,X1),k10_yellow_6(X2,X4))
    | r2_hidden(esk3_3(X2,X3,X1),X1)
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
    inference(spm,[status(thm)],[c_0_85,c_0_37])).

cnf(c_0_115,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk8_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_116,negated_conjecture,
    ( v3_yellow_6(esk8_1(esk9_0),esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | ~ v3_yellow_6(esk11_1(esk8_1(esk9_0)),esk9_0)
    | ~ l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_117,negated_conjecture,
    ( v3_yellow_6(esk11_1(X1),esk9_0)
    | v2_struct_0(X1)
    | v1_compts_1(esk9_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_118,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_hidden(esk3_3(X1,X2,k1_xboole_0),k10_yellow_6(X1,X3))
    | k10_yellow_6(X1,X3) != k10_yellow_6(X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_86]),c_0_87])).

cnf(c_0_119,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,k10_yellow_6(X1,esk8_1(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_54]),c_0_55]),c_0_109]),c_0_107]),c_0_99]),c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( v3_yellow_6(esk8_1(esk9_0),esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | ~ l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_78])).

cnf(c_0_121,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k10_yellow_6(X1,X3) != k10_yellow_6(X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k10_yellow_6(X1,X3),esk3_3(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_118])).

cnf(c_0_122,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(X1,esk8_1(X1)),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_119,c_0_62])).

cnf(c_0_123,negated_conjecture,
    ( v1_compts_1(esk9_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_struct_0(esk11_1(X1))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_67]),c_0_41])).

cnf(c_0_124,negated_conjecture,
    ( v3_yellow_6(esk8_1(esk9_0),esk9_0)
    | v2_struct_0(esk11_1(esk8_1(esk9_0)))
    | v2_struct_0(esk8_1(esk9_0))
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_97]),c_0_78])).

cnf(c_0_125,plain,
    ( k10_yellow_6(X1,X2) = k1_xboole_0
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k10_yellow_6(X1,esk8_1(X1)) != k10_yellow_6(X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_109]),c_0_107]),c_0_99]),c_0_115])).

cnf(c_0_126,negated_conjecture,
    ( v3_yellow_6(esk8_1(esk9_0),esk9_0)
    | v2_struct_0(esk8_1(esk9_0))
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ v7_waybel_0(esk11_1(esk8_1(esk9_0)))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_78])).

cnf(c_0_127,plain,
    ( k10_yellow_6(X1,esk8_1(X1)) = k1_xboole_0
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_125]),c_0_109]),c_0_107]),c_0_99]),c_0_115])).

cnf(c_0_128,negated_conjecture,
    ( v3_yellow_6(esk8_1(esk9_0),esk9_0)
    | v2_struct_0(esk8_1(esk9_0))
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk11_1(esk8_1(esk9_0)))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_101]),c_0_78])).

cnf(c_0_129,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v3_yellow_6(esk8_1(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_127]),c_0_109]),c_0_107]),c_0_99]),c_0_115])).

cnf(c_0_130,negated_conjecture,
    ( v3_yellow_6(esk8_1(esk9_0),esk9_0)
    | v2_struct_0(esk8_1(esk9_0))
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_104]),c_0_78])).

cnf(c_0_131,negated_conjecture,
    ( v2_struct_0(esk8_1(esk9_0))
    | ~ l1_waybel_0(esk8_1(esk9_0),esk9_0)
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_132,negated_conjecture,
    ( v2_struct_0(esk8_1(esk9_0))
    | ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_99]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_133,negated_conjecture,
    ( ~ v7_waybel_0(esk8_1(esk9_0))
    | ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_132]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_134,negated_conjecture,
    ( ~ v4_orders_2(esk8_1(esk9_0))
    | ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_107]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_135,negated_conjecture,
    ( ~ l1_struct_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_109]),c_0_39]),c_0_40])]),c_0_78]),c_0_41])).

cnf(c_0_136,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_30]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.63  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.39/0.63  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.39/0.63  #
% 0.39/0.63  # Preprocessing time       : 0.044 s
% 0.39/0.63  # Presaturation interreduction done
% 0.39/0.63  
% 0.39/0.63  # Proof found!
% 0.39/0.63  # SZS status Theorem
% 0.39/0.63  # SZS output start CNFRefutation
% 0.39/0.63  fof(t37_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 0.39/0.63  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.39/0.63  fof(t32_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r3_waybel_9(X1,X2,X3)&![X4]:(m2_yellow_6(X4,X1,X2)=>~(r2_hidden(X3,k10_yellow_6(X1,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 0.39/0.63  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.39/0.63  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.39/0.63  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.39/0.63  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.39/0.63  fof(d19_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v3_yellow_6(X2,X1)<=>k10_yellow_6(X1,X2)!=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 0.39/0.63  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.39/0.63  fof(d9_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>![X4]:(m1_connsp_2(X4,X1,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_waybel_9)).
% 0.39/0.63  fof(t29_waybel_9, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))=>r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 0.39/0.63  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.39/0.63  fof(t35_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_yellow19)).
% 0.39/0.63  fof(t27_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(r2_waybel_0(X1,X3,X4)=>r2_waybel_0(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_6)).
% 0.39/0.63  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.39/0.63  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.39/0.63  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>(v1_compts_1(X1)<=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m2_yellow_6(X3,X1,X2)&v3_yellow_6(X3,X1)))))), inference(assume_negation,[status(cth)],[t37_yellow19])).
% 0.39/0.63  fof(c_0_17, plain, ![X17, X18]:(~r2_hidden(X17,X18)|~r1_tarski(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.39/0.63  fof(c_0_18, plain, ![X48, X49, X50]:((m2_yellow_6(esk6_3(X48,X49,X50),X48,X49)|~r3_waybel_9(X48,X49,X50)|~m1_subset_1(X50,u1_struct_0(X48))|(v2_struct_0(X49)|~v4_orders_2(X49)|~v7_waybel_0(X49)|~l1_waybel_0(X49,X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(r2_hidden(X50,k10_yellow_6(X48,esk6_3(X48,X49,X50)))|~r3_waybel_9(X48,X49,X50)|~m1_subset_1(X50,u1_struct_0(X48))|(v2_struct_0(X49)|~v4_orders_2(X49)|~v7_waybel_0(X49)|~l1_waybel_0(X49,X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_waybel_9])])])])])])).
% 0.39/0.63  fof(c_0_19, plain, ![X31, X32, X33]:((((~v2_struct_0(X33)|~m2_yellow_6(X33,X31,X32)|(v2_struct_0(X31)|~l1_struct_0(X31)|v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31)))&(v4_orders_2(X33)|~m2_yellow_6(X33,X31,X32)|(v2_struct_0(X31)|~l1_struct_0(X31)|v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31))))&(v7_waybel_0(X33)|~m2_yellow_6(X33,X31,X32)|(v2_struct_0(X31)|~l1_struct_0(X31)|v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31))))&(l1_waybel_0(X33,X31)|~m2_yellow_6(X33,X31,X32)|(v2_struct_0(X31)|~l1_struct_0(X31)|v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.39/0.63  fof(c_0_20, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.39/0.63  fof(c_0_21, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|m1_subset_1(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.39/0.63  fof(c_0_22, plain, ![X29, X30]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~v4_orders_2(X30)|~v7_waybel_0(X30)|~l1_waybel_0(X30,X29)|m1_subset_1(k10_yellow_6(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.39/0.63  fof(c_0_23, negated_conjecture, ![X59, X60]:(((~v2_struct_0(esk9_0)&v2_pre_topc(esk9_0))&l1_pre_topc(esk9_0))&((((((~v2_struct_0(esk10_0)|~v1_compts_1(esk9_0))&(v4_orders_2(esk10_0)|~v1_compts_1(esk9_0)))&(v7_waybel_0(esk10_0)|~v1_compts_1(esk9_0)))&(l1_waybel_0(esk10_0,esk9_0)|~v1_compts_1(esk9_0)))&(~m2_yellow_6(X59,esk9_0,esk10_0)|~v3_yellow_6(X59,esk9_0)|~v1_compts_1(esk9_0)))&((m2_yellow_6(esk11_1(X60),esk9_0,X60)|(v2_struct_0(X60)|~v4_orders_2(X60)|~v7_waybel_0(X60)|~l1_waybel_0(X60,esk9_0))|v1_compts_1(esk9_0))&(v3_yellow_6(esk11_1(X60),esk9_0)|(v2_struct_0(X60)|~v4_orders_2(X60)|~v7_waybel_0(X60)|~l1_waybel_0(X60,esk9_0))|v1_compts_1(esk9_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).
% 0.39/0.63  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.63  cnf(c_0_25, plain, (r2_hidden(X1,k10_yellow_6(X2,esk6_3(X2,X3,X1)))|v2_struct_0(X3)|v2_struct_0(X2)|~r3_waybel_9(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.63  fof(c_0_26, plain, ![X38, X39]:((~v3_yellow_6(X39,X38)|k10_yellow_6(X38,X39)!=k1_xboole_0|(v2_struct_0(X39)|~v4_orders_2(X39)|~v7_waybel_0(X39)|~l1_waybel_0(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(k10_yellow_6(X38,X39)=k1_xboole_0|v3_yellow_6(X39,X38)|(v2_struct_0(X39)|~v4_orders_2(X39)|~v7_waybel_0(X39)|~l1_waybel_0(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d19_yellow_6])])])])])).
% 0.39/0.63  fof(c_0_27, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.39/0.63  cnf(c_0_28, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.63  cnf(c_0_29, plain, (m2_yellow_6(esk6_3(X1,X2,X3),X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.63  cnf(c_0_30, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.39/0.63  cnf(c_0_31, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.63  cnf(c_0_32, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.63  cnf(c_0_33, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.63  fof(c_0_34, plain, ![X40, X41, X42, X43]:((~r3_waybel_9(X40,X41,X42)|(~m1_connsp_2(X43,X40,X42)|r2_waybel_0(X40,X41,X43))|~m1_subset_1(X42,u1_struct_0(X40))|(v2_struct_0(X41)|~l1_waybel_0(X41,X40))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&((m1_connsp_2(esk5_3(X40,X41,X42),X40,X42)|r3_waybel_9(X40,X41,X42)|~m1_subset_1(X42,u1_struct_0(X40))|(v2_struct_0(X41)|~l1_waybel_0(X41,X40))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(~r2_waybel_0(X40,X41,esk5_3(X40,X41,X42))|r3_waybel_9(X40,X41,X42)|~m1_subset_1(X42,u1_struct_0(X40))|(v2_struct_0(X41)|~l1_waybel_0(X41,X40))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).
% 0.39/0.63  fof(c_0_35, plain, ![X45, X46, X47]:(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(v2_struct_0(X46)|~v4_orders_2(X46)|~v7_waybel_0(X46)|~l1_waybel_0(X46,X45)|(~m1_subset_1(X47,u1_struct_0(X45))|(~r2_hidden(X47,k10_yellow_6(X45,X46))|r3_waybel_9(X45,X46,X47))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_waybel_9])])])])).
% 0.39/0.63  cnf(c_0_36, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.39/0.63  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.63  cnf(c_0_38, negated_conjecture, (~m2_yellow_6(X1,esk9_0,esk10_0)|~v3_yellow_6(X1,esk9_0)|~v1_compts_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_42, negated_conjecture, (v4_orders_2(esk10_0)|~v1_compts_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_43, negated_conjecture, (v7_waybel_0(esk10_0)|~v1_compts_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_44, negated_conjecture, (l1_waybel_0(esk10_0,esk9_0)|~v1_compts_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk10_0)|~v1_compts_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_46, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(k10_yellow_6(X1,esk6_3(X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.39/0.63  cnf(c_0_47, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v3_yellow_6(X2,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.63  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.63  cnf(c_0_49, plain, (v4_orders_2(esk6_3(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.39/0.63  cnf(c_0_50, plain, (v7_waybel_0(esk6_3(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_30])).
% 0.39/0.63  cnf(c_0_51, plain, (l1_waybel_0(esk6_3(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_30])).
% 0.39/0.63  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~v2_struct_0(esk6_3(X1,X2,X3))|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_30])).
% 0.39/0.63  cnf(c_0_53, plain, (r2_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_connsp_2(X4,X1,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.63  cnf(c_0_54, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r3_waybel_9(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.39/0.63  cnf(c_0_55, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X3,k10_yellow_6(X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.39/0.63  fof(c_0_56, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.39/0.63  cnf(c_0_57, negated_conjecture, (~v1_compts_1(esk9_0)|~r3_waybel_9(esk9_0,esk10_0,X1)|~v3_yellow_6(esk6_3(esk9_0,esk10_0,X1),esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_29]), c_0_39]), c_0_40])]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.39/0.63  cnf(c_0_58, plain, (v3_yellow_6(esk6_3(X1,X2,X3),X1)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.39/0.63  fof(c_0_59, plain, ![X52, X53, X56]:(((m1_subset_1(esk7_2(X52,X53),u1_struct_0(X52))|(v2_struct_0(X53)|~v4_orders_2(X53)|~v7_waybel_0(X53)|~l1_waybel_0(X53,X52))|~v1_compts_1(X52)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52)))&(r3_waybel_9(X52,X53,esk7_2(X52,X53))|(v2_struct_0(X53)|~v4_orders_2(X53)|~v7_waybel_0(X53)|~l1_waybel_0(X53,X52))|~v1_compts_1(X52)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52))))&(((((~v2_struct_0(esk8_1(X52))|v1_compts_1(X52)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52)))&(v4_orders_2(esk8_1(X52))|v1_compts_1(X52)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52))))&(v7_waybel_0(esk8_1(X52))|v1_compts_1(X52)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52))))&(l1_waybel_0(esk8_1(X52),X52)|v1_compts_1(X52)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52))))&(~m1_subset_1(X56,u1_struct_0(X52))|~r3_waybel_9(X52,esk8_1(X52),X56)|v1_compts_1(X52)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_yellow19])])])])])])).
% 0.39/0.63  fof(c_0_60, plain, ![X34, X35, X36, X37]:(v2_struct_0(X34)|~l1_struct_0(X34)|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34)|(~m2_yellow_6(X36,X34,X35)|(~r2_waybel_0(X34,X36,X37)|r2_waybel_0(X34,X35,X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).
% 0.39/0.63  cnf(c_0_61, plain, (r2_waybel_0(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_connsp_2(X3,X1,X4)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X4,k10_yellow_6(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.39/0.63  cnf(c_0_62, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.39/0.63  cnf(c_0_63, negated_conjecture, (~v1_compts_1(esk9_0)|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_39]), c_0_40])]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.39/0.63  cnf(c_0_64, plain, (r3_waybel_9(X1,X2,esk7_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.39/0.63  fof(c_0_65, plain, ![X20, X21, X22, X23, X24, X28]:(((~r2_hidden(X23,X22)|(~m1_connsp_2(X24,X20,X23)|r1_waybel_0(X20,X21,X24))|~m1_subset_1(X23,u1_struct_0(X20))|X22!=k10_yellow_6(X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((m1_connsp_2(esk2_4(X20,X21,X22,X23),X20,X23)|r2_hidden(X23,X22)|~m1_subset_1(X23,u1_struct_0(X20))|X22!=k10_yellow_6(X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r1_waybel_0(X20,X21,esk2_4(X20,X21,X22,X23))|r2_hidden(X23,X22)|~m1_subset_1(X23,u1_struct_0(X20))|X22!=k10_yellow_6(X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))))&((m1_subset_1(esk3_3(X20,X21,X22),u1_struct_0(X20))|X22=k10_yellow_6(X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(((m1_connsp_2(esk4_3(X20,X21,X22),X20,esk3_3(X20,X21,X22))|~r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k10_yellow_6(X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r1_waybel_0(X20,X21,esk4_3(X20,X21,X22))|~r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k10_yellow_6(X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))))&(r2_hidden(esk3_3(X20,X21,X22),X22)|(~m1_connsp_2(X28,X20,esk3_3(X20,X21,X22))|r1_waybel_0(X20,X21,X28))|X22=k10_yellow_6(X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.39/0.63  cnf(c_0_66, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_waybel_0(X1,X2,X4)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~r2_waybel_0(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.39/0.63  cnf(c_0_67, negated_conjecture, (m2_yellow_6(esk11_1(X1),esk9_0,X1)|v2_struct_0(X1)|v1_compts_1(esk9_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_68, plain, (r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|r1_tarski(k10_yellow_6(X1,X2),X4)|~m1_connsp_2(X3,X1,esk1_2(k10_yellow_6(X1,X2),X4))|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.39/0.63  cnf(c_0_69, plain, (m1_connsp_2(esk5_3(X1,X2,X3),X1,X3)|r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.63  cnf(c_0_70, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk1_2(k10_yellow_6(X2,X1),X3),u1_struct_0(X2))|r1_tarski(k10_yellow_6(X2,X1),X3)|~l1_waybel_0(X1,X2)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_55, c_0_62])).
% 0.39/0.63  cnf(c_0_71, negated_conjecture, (~v1_compts_1(esk9_0)|~m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_39]), c_0_40])]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.39/0.63  cnf(c_0_72, plain, (m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v1_compts_1(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.39/0.63  cnf(c_0_73, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|r1_waybel_0(X1,X2,X4)|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X4,X1,esk3_3(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.39/0.63  cnf(c_0_74, plain, (m1_connsp_2(esk2_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.39/0.63  cnf(c_0_75, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|X3=k10_yellow_6(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.39/0.63  cnf(c_0_76, negated_conjecture, (v1_compts_1(esk9_0)|r2_waybel_0(esk9_0,X1,X2)|v2_struct_0(X1)|~r2_waybel_0(esk9_0,esk11_1(X1),X2)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_41])).
% 0.39/0.63  cnf(c_0_77, plain, (r3_waybel_9(X1,X2,esk1_2(k10_yellow_6(X1,X3),X4))|r2_waybel_0(X1,X3,esk5_3(X1,X2,esk1_2(k10_yellow_6(X1,X3),X4)))|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|r1_tarski(k10_yellow_6(X1,X3),X4)|~l1_waybel_0(X3,X1)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.39/0.63  cnf(c_0_78, negated_conjecture, (~v1_compts_1(esk9_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_39]), c_0_40])]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.39/0.63  cnf(c_0_79, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.39/0.63  cnf(c_0_80, plain, (X1=k10_yellow_6(X2,X3)|r1_waybel_0(X2,X3,esk2_4(X2,X4,X5,esk3_3(X2,X3,X1)))|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk3_3(X2,X3,X1),X5)|r2_hidden(esk3_3(X2,X3,X1),X1)|X5!=k10_yellow_6(X2,X4)|~l1_waybel_0(X3,X2)|~l1_waybel_0(X4,X2)|~v7_waybel_0(X3)|~v7_waybel_0(X4)|~v4_orders_2(X3)|~v4_orders_2(X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.39/0.63  fof(c_0_81, plain, ![X13]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.39/0.63  cnf(c_0_82, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.39/0.63  cnf(c_0_83, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_0(X1,X2,esk5_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.63  cnf(c_0_84, negated_conjecture, (r3_waybel_9(esk9_0,X1,esk1_2(k10_yellow_6(esk9_0,esk11_1(X2)),X3))|r2_waybel_0(esk9_0,X2,esk5_3(esk9_0,X1,esk1_2(k10_yellow_6(esk9_0,esk11_1(X2)),X3)))|v2_struct_0(esk11_1(X2))|v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(k10_yellow_6(esk9_0,esk11_1(X2)),X3)|~l1_waybel_0(esk11_1(X2),esk9_0)|~l1_waybel_0(X2,esk9_0)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk11_1(X2))|~v7_waybel_0(X2)|~v4_orders_2(esk11_1(X2))|~v4_orders_2(X2)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_85, plain, (X1=k10_yellow_6(X2,X3)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk3_3(X2,X3,X1),X1)|r2_hidden(esk3_3(X2,X3,X1),X4)|X4!=k10_yellow_6(X2,X3)|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_75])).
% 0.39/0.63  cnf(c_0_86, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.39/0.63  cnf(c_0_87, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_48])).
% 0.39/0.63  cnf(c_0_88, plain, (v1_compts_1(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_waybel_9(X2,esk8_1(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.39/0.63  cnf(c_0_89, negated_conjecture, (r3_waybel_9(esk9_0,X1,esk1_2(k10_yellow_6(esk9_0,esk11_1(X1)),X2))|v2_struct_0(esk11_1(X1))|v2_struct_0(X1)|r1_tarski(k10_yellow_6(esk9_0,esk11_1(X1)),X2)|~l1_waybel_0(esk11_1(X1),esk9_0)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk11_1(X1))|~v7_waybel_0(X1)|~v4_orders_2(esk11_1(X1))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)|~m1_subset_1(esk1_2(k10_yellow_6(esk9_0,esk11_1(X1)),X2),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_39]), c_0_40])]), c_0_41])).
% 0.39/0.63  cnf(c_0_90, plain, (X1=k10_yellow_6(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|r2_hidden(esk3_3(X2,X3,X1),X1)|k10_yellow_6(X2,X3)!=k1_xboole_0|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.39/0.63  cnf(c_0_91, negated_conjecture, (v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|r1_tarski(k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))),X1)|~l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)|~m1_subset_1(esk1_2(k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))),X1),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_92, plain, (X1=k10_yellow_6(X2,X3)|v2_struct_0(X2)|v2_struct_0(X3)|k10_yellow_6(X2,X3)!=k1_xboole_0|~l1_waybel_0(X3,X2)|~v7_waybel_0(X3)|~v4_orders_2(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,esk3_3(X2,X3,X1))), inference(spm,[status(thm)],[c_0_24, c_0_90])).
% 0.39/0.63  cnf(c_0_93, negated_conjecture, (v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|r1_tarski(k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))),X1)|~l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_70]), c_0_39]), c_0_40])]), c_0_41])).
% 0.39/0.63  cnf(c_0_94, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k10_yellow_6(X1,X2)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X2)|v2_struct_0(X1)|k10_yellow_6(X1,X2)!=k1_xboole_0|~l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~l1_waybel_0(X2,X1)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v7_waybel_0(X2)|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_struct_0(esk9_0)|~l1_pre_topc(X1)|~m1_subset_1(k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0))),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.39/0.63  cnf(c_0_95, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k10_yellow_6(esk9_0,X1)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|k10_yellow_6(esk9_0,X1)!=k1_xboole_0|~l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_37]), c_0_39]), c_0_40])]), c_0_41])).
% 0.39/0.63  cnf(c_0_96, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_47]), c_0_39]), c_0_40])]), c_0_41])).
% 0.39/0.63  cnf(c_0_97, negated_conjecture, (v1_compts_1(esk9_0)|l1_waybel_0(esk11_1(X1),esk9_0)|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_67]), c_0_41])).
% 0.39/0.63  cnf(c_0_98, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_78])).
% 0.39/0.63  cnf(c_0_99, plain, (l1_waybel_0(esk8_1(X1),X1)|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.39/0.63  cnf(c_0_100, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_101, negated_conjecture, (v1_compts_1(esk9_0)|v7_waybel_0(esk11_1(X1))|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_67]), c_0_41])).
% 0.39/0.63  cnf(c_0_102, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk8_1(esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_78])).
% 0.39/0.63  cnf(c_0_103, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk8_1(esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_99]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_104, negated_conjecture, (v1_compts_1(esk9_0)|v4_orders_2(esk11_1(X1))|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_67]), c_0_41])).
% 0.39/0.63  cnf(c_0_105, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk8_1(esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_78])).
% 0.39/0.63  cnf(c_0_106, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(esk8_1(esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_99]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_107, plain, (v7_waybel_0(esk8_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.39/0.63  cnf(c_0_108, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(esk8_1(esk9_0))|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_109, plain, (v4_orders_2(esk8_1(X1))|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.39/0.63  cnf(c_0_110, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_111, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(X1,esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_30]), c_0_40])])).
% 0.39/0.63  cnf(c_0_112, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v3_yellow_6(X1,X2)|k10_yellow_6(X2,X1)!=k1_xboole_0|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.63  cnf(c_0_113, negated_conjecture, (k10_yellow_6(esk9_0,esk11_1(esk8_1(esk9_0)))=k1_xboole_0|v3_yellow_6(esk8_1(esk9_0),esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk8_1(esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_99]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_114, plain, (X1=k10_yellow_6(X2,X3)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|r2_hidden(esk3_3(X2,X3,X1),k10_yellow_6(X2,X4))|r2_hidden(esk3_3(X2,X3,X1),X1)|k10_yellow_6(X2,X4)!=k10_yellow_6(X2,X3)|~l1_waybel_0(X3,X2)|~l1_waybel_0(X4,X2)|~v7_waybel_0(X3)|~v7_waybel_0(X4)|~v4_orders_2(X3)|~v4_orders_2(X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_85, c_0_37])).
% 0.39/0.63  cnf(c_0_115, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_struct_0(esk8_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.39/0.63  cnf(c_0_116, negated_conjecture, (v3_yellow_6(esk8_1(esk9_0),esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|~v3_yellow_6(esk11_1(esk8_1(esk9_0)),esk9_0)|~l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_39]), c_0_40])]), c_0_41])).
% 0.39/0.63  cnf(c_0_117, negated_conjecture, (v3_yellow_6(esk11_1(X1),esk9_0)|v2_struct_0(X1)|v1_compts_1(esk9_0)|~v4_orders_2(X1)|~v7_waybel_0(X1)|~l1_waybel_0(X1,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.63  cnf(c_0_118, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_hidden(esk3_3(X1,X2,k1_xboole_0),k10_yellow_6(X1,X3))|k10_yellow_6(X1,X3)!=k10_yellow_6(X1,X2)|~l1_waybel_0(X2,X1)|~l1_waybel_0(X3,X1)|~v7_waybel_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X2)|~v4_orders_2(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_86]), c_0_87])).
% 0.39/0.63  cnf(c_0_119, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X2,k10_yellow_6(X1,esk8_1(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_54]), c_0_55]), c_0_109]), c_0_107]), c_0_99]), c_0_115])).
% 0.39/0.63  cnf(c_0_120, negated_conjecture, (v3_yellow_6(esk8_1(esk9_0),esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|~l1_waybel_0(esk11_1(esk8_1(esk9_0)),esk9_0)|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_78])).
% 0.39/0.63  cnf(c_0_121, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|k10_yellow_6(X1,X3)!=k10_yellow_6(X1,X2)|~l1_waybel_0(X2,X1)|~l1_waybel_0(X3,X1)|~v7_waybel_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X2)|~v4_orders_2(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r1_tarski(k10_yellow_6(X1,X3),esk3_3(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_24, c_0_118])).
% 0.39/0.63  cnf(c_0_122, plain, (v1_compts_1(X1)|v2_struct_0(X1)|r1_tarski(k10_yellow_6(X1,esk8_1(X1)),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_119, c_0_62])).
% 0.39/0.63  cnf(c_0_123, negated_conjecture, (v1_compts_1(esk9_0)|v2_struct_0(X1)|~l1_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_struct_0(esk11_1(X1))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_67]), c_0_41])).
% 0.39/0.63  cnf(c_0_124, negated_conjecture, (v3_yellow_6(esk8_1(esk9_0),esk9_0)|v2_struct_0(esk11_1(esk8_1(esk9_0)))|v2_struct_0(esk8_1(esk9_0))|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_97]), c_0_78])).
% 0.39/0.63  cnf(c_0_125, plain, (k10_yellow_6(X1,X2)=k1_xboole_0|v1_compts_1(X1)|v2_struct_0(X1)|v2_struct_0(X2)|k10_yellow_6(X1,esk8_1(X1))!=k10_yellow_6(X1,X2)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_109]), c_0_107]), c_0_99]), c_0_115])).
% 0.39/0.63  cnf(c_0_126, negated_conjecture, (v3_yellow_6(esk8_1(esk9_0),esk9_0)|v2_struct_0(esk8_1(esk9_0))|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~v7_waybel_0(esk11_1(esk8_1(esk9_0)))|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_78])).
% 0.39/0.63  cnf(c_0_127, plain, (k10_yellow_6(X1,esk8_1(X1))=k1_xboole_0|v1_compts_1(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_125]), c_0_109]), c_0_107]), c_0_99]), c_0_115])).
% 0.39/0.63  cnf(c_0_128, negated_conjecture, (v3_yellow_6(esk8_1(esk9_0),esk9_0)|v2_struct_0(esk8_1(esk9_0))|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk11_1(esk8_1(esk9_0)))|~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_101]), c_0_78])).
% 0.39/0.63  cnf(c_0_129, plain, (v1_compts_1(X1)|v2_struct_0(X1)|~v3_yellow_6(esk8_1(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_127]), c_0_109]), c_0_107]), c_0_99]), c_0_115])).
% 0.39/0.63  cnf(c_0_130, negated_conjecture, (v3_yellow_6(esk8_1(esk9_0),esk9_0)|v2_struct_0(esk8_1(esk9_0))|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_104]), c_0_78])).
% 0.39/0.63  cnf(c_0_131, negated_conjecture, (v2_struct_0(esk8_1(esk9_0))|~l1_waybel_0(esk8_1(esk9_0),esk9_0)|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_132, negated_conjecture, (v2_struct_0(esk8_1(esk9_0))|~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_99]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_133, negated_conjecture, (~v7_waybel_0(esk8_1(esk9_0))|~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_132]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_134, negated_conjecture, (~v4_orders_2(esk8_1(esk9_0))|~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_107]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_135, negated_conjecture, (~l1_struct_0(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_109]), c_0_39]), c_0_40])]), c_0_78]), c_0_41])).
% 0.39/0.63  cnf(c_0_136, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_30]), c_0_40])]), ['proof']).
% 0.39/0.63  # SZS output end CNFRefutation
% 0.39/0.63  # Proof object total steps             : 137
% 0.39/0.63  # Proof object clause steps            : 104
% 0.39/0.63  # Proof object formula steps           : 33
% 0.39/0.63  # Proof object conjectures             : 51
% 0.39/0.63  # Proof object clause conjectures      : 48
% 0.39/0.63  # Proof object formula conjectures     : 3
% 0.39/0.63  # Proof object initial clauses used    : 42
% 0.39/0.63  # Proof object initial formulas used   : 16
% 0.39/0.63  # Proof object generating inferences   : 62
% 0.39/0.63  # Proof object simplifying inferences  : 167
% 0.39/0.63  # Training examples: 0 positive, 0 negative
% 0.39/0.63  # Parsed axioms                        : 16
% 0.39/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.63  # Initial clauses                      : 46
% 0.39/0.63  # Removed in clause preprocessing      : 0
% 0.39/0.63  # Initial clauses in saturation        : 46
% 0.39/0.63  # Processed clauses                    : 602
% 0.39/0.63  # ...of these trivial                  : 0
% 0.39/0.63  # ...subsumed                          : 113
% 0.39/0.63  # ...remaining for further processing  : 489
% 0.39/0.63  # Other redundant clauses eliminated   : 0
% 0.39/0.63  # Clauses deleted for lack of memory   : 0
% 0.39/0.63  # Backward-subsumed                    : 221
% 0.39/0.63  # Backward-rewritten                   : 0
% 0.39/0.63  # Generated clauses                    : 869
% 0.39/0.63  # ...of the previous two non-trivial   : 634
% 0.39/0.63  # Contextual simplify-reflections      : 127
% 0.39/0.63  # Paramodulations                      : 867
% 0.39/0.63  # Factorizations                       : 0
% 0.39/0.63  # Equation resolutions                 : 2
% 0.39/0.63  # Propositional unsat checks           : 0
% 0.39/0.63  #    Propositional check models        : 0
% 0.39/0.63  #    Propositional check unsatisfiable : 0
% 0.39/0.63  #    Propositional clauses             : 0
% 0.39/0.63  #    Propositional clauses after purity: 0
% 0.39/0.63  #    Propositional unsat core size     : 0
% 0.39/0.63  #    Propositional preprocessing time  : 0.000
% 0.39/0.63  #    Propositional encoding time       : 0.000
% 0.39/0.63  #    Propositional solver time         : 0.000
% 0.39/0.63  #    Success case prop preproc time    : 0.000
% 0.39/0.63  #    Success case prop encoding time   : 0.000
% 0.39/0.63  #    Success case prop solver time     : 0.000
% 0.39/0.63  # Current number of processed clauses  : 222
% 0.39/0.63  #    Positive orientable unit clauses  : 5
% 0.39/0.63  #    Positive unorientable unit clauses: 0
% 0.39/0.63  #    Negative unit clauses             : 3
% 0.39/0.63  #    Non-unit-clauses                  : 214
% 0.39/0.63  # Current number of unprocessed clauses: 114
% 0.39/0.63  # ...number of literals in the above   : 2470
% 0.39/0.63  # Current number of archived formulas  : 0
% 0.39/0.63  # Current number of archived clauses   : 267
% 0.39/0.63  # Clause-clause subsumption calls (NU) : 97066
% 0.39/0.63  # Rec. Clause-clause subsumption calls : 3842
% 0.39/0.63  # Non-unit clause-clause subsumptions  : 436
% 0.39/0.63  # Unit Clause-clause subsumption calls : 195
% 0.39/0.63  # Rewrite failures with RHS unbound    : 0
% 0.39/0.63  # BW rewrite match attempts            : 5
% 0.39/0.63  # BW rewrite match successes           : 0
% 0.39/0.63  # Condensation attempts                : 0
% 0.39/0.63  # Condensation successes               : 0
% 0.39/0.63  # Termbank termtop insertions          : 83581
% 0.39/0.63  
% 0.39/0.63  # -------------------------------------------------
% 0.39/0.63  # User time                : 0.283 s
% 0.39/0.63  # System time              : 0.008 s
% 0.39/0.63  # Total time               : 0.291 s
% 0.39/0.63  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
