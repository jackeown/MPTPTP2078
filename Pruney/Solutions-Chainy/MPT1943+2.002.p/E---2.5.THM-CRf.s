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
% DateTime   : Thu Dec  3 11:21:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 721 expanded)
%              Number of clauses        :   47 ( 232 expanded)
%              Number of leaves         :    8 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  457 (5257 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   81 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_yellow_6,conjecture,(
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
             => r1_tarski(k10_yellow_6(X1,X2),k10_yellow_6(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_yellow_6)).

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

fof(t9_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ~ r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
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
               => r1_tarski(k10_yellow_6(X1,X2),k10_yellow_6(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_yellow_6])).

fof(c_0_9,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v4_orders_2(esk6_0)
    & v7_waybel_0(esk6_0)
    & l1_waybel_0(esk6_0,esk5_0)
    & m2_yellow_6(esk7_0,esk5_0,esk6_0)
    & ~ r1_tarski(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_struct_0(X27)
        | ~ m2_yellow_6(X27,X25,X26)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25) )
      & ( v4_orders_2(X27)
        | ~ m2_yellow_6(X27,X25,X26)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25) )
      & ( v7_waybel_0(X27)
        | ~ m2_yellow_6(X27,X25,X26)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25) )
      & ( l1_waybel_0(X27,X25)
        | ~ m2_yellow_6(X27,X25,X26)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25)
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_12,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X28,X29,X30,X31] :
      ( v2_struct_0(X28)
      | ~ l1_struct_0(X28)
      | v2_struct_0(X29)
      | ~ v4_orders_2(X29)
      | ~ v7_waybel_0(X29)
      | ~ l1_waybel_0(X29,X28)
      | ~ m2_yellow_6(X30,X28,X29)
      | ~ r2_waybel_0(X28,X30,X31)
      | r2_waybel_0(X28,X29,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r1_waybel_0(X11,X12,X13)
        | ~ r2_waybel_0(X11,X12,k6_subset_1(u1_struct_0(X11),X13))
        | v2_struct_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11) )
      & ( r2_waybel_0(X11,X12,k6_subset_1(u1_struct_0(X11),X13))
        | r1_waybel_0(X11,X12,X13)
        | v2_struct_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).

cnf(c_0_16,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m2_yellow_6(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v7_waybel_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_24,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23])])).

fof(c_0_29,plain,(
    ! [X14,X15,X16,X17,X18,X22] :
      ( ( ~ r2_hidden(X17,X16)
        | ~ m1_connsp_2(X18,X14,X17)
        | r1_waybel_0(X14,X15,X18)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | X16 != k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_connsp_2(esk2_4(X14,X15,X16,X17),X14,X17)
        | r2_hidden(X17,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | X16 != k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r1_waybel_0(X14,X15,esk2_4(X14,X15,X16,X17))
        | r2_hidden(X17,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | X16 != k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_3(X14,X15,X16),u1_struct_0(X14))
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_connsp_2(esk4_3(X14,X15,X16),X14,esk3_3(X14,X15,X16))
        | ~ r2_hidden(esk3_3(X14,X15,X16),X16)
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r1_waybel_0(X14,X15,esk4_3(X14,X15,X16))
        | ~ r2_hidden(esk3_3(X14,X15,X16),X16)
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk3_3(X14,X15,X16),X16)
        | ~ m1_connsp_2(X22,X14,esk3_3(X14,X15,X16))
        | r1_waybel_0(X14,X15,X22)
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_30,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ v4_orders_2(X24)
      | ~ v7_waybel_0(X24)
      | ~ l1_waybel_0(X24,X23)
      | m1_subset_1(k10_yellow_6(X23,X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_31,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,X1)
    | ~ r2_waybel_0(esk5_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_32,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk7_0,k6_subset_1(u1_struct_0(esk5_0),X1))
    | r1_waybel_0(esk5_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23])]),c_0_28]),c_0_22])).

cnf(c_0_33,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r1_waybel_0(X4,X5,X3)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_connsp_2(X3,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | X2 != k10_yellow_6(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v4_orders_2(X5)
    | ~ v7_waybel_0(X5)
    | ~ l1_waybel_0(X5,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X6,X7,X8] :
      ( ( m1_subset_1(esk1_3(X6,X7,X8),X6)
        | r1_tarski(X7,X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X7)
        | r1_tarski(X7,X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) )
      & ( ~ r2_hidden(esk1_3(X6,X7,X8),X8)
        | r1_tarski(X7,X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_38,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,k6_subset_1(u1_struct_0(esk5_0),X1))
    | r1_waybel_0(esk5_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( v7_waybel_0(esk7_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( v4_orders_2(esk7_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_43,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X4)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X4,k10_yellow_6(X1,X2))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(X3,k10_yellow_6(X2,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_pre_topc(X2)
    | ~ r1_waybel_0(X2,X1,esk2_4(X2,X1,k10_yellow_6(X2,X1),X3))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk7_0,X1)
    | ~ r1_waybel_0(esk5_0,esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_20]),c_0_23])]),c_0_21]),c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( v7_waybel_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_23])])).

cnf(c_0_49,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_23])])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_tarski(k10_yellow_6(X1,X2),X4)
    | ~ m1_connsp_2(X3,X1,esk1_3(X5,k10_yellow_6(X1,X2),X4))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk1_3(X5,k10_yellow_6(X1,X2),X4),u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(X5))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( m1_connsp_2(esk2_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk5_0,esk7_0))
    | ~ r1_waybel_0(esk5_0,esk6_0,esk2_4(esk5_0,esk7_0,k10_yellow_6(esk5_0,esk7_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_27]),c_0_13])]),c_0_22]),c_0_28])).

cnf(c_0_54,plain,
    ( r1_waybel_0(X1,X2,esk2_4(X1,X3,k10_yellow_6(X1,X3),esk1_3(X4,k10_yellow_6(X1,X2),X5)))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tarski(k10_yellow_6(X1,X2),X5)
    | r2_hidden(esk1_3(X4,k10_yellow_6(X1,X2),X5),k10_yellow_6(X1,X3))
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk1_3(X4,k10_yellow_6(X1,X2),X5),u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k10_yellow_6(esk5_0,esk6_0),X1)
    | r2_hidden(esk1_3(X2,k10_yellow_6(esk5_0,esk6_0),X1),k10_yellow_6(esk5_0,esk7_0))
    | ~ m1_subset_1(esk1_3(X2,k10_yellow_6(esk5_0,esk6_0),X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(k10_yellow_6(esk5_0,esk6_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_18]),c_0_48]),c_0_19]),c_0_49]),c_0_50]),c_0_20]),c_0_27]),c_0_13])]),c_0_28]),c_0_22]),c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(X1,k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0)),u1_struct_0(esk5_0))
    | ~ m1_subset_1(k10_yellow_6(esk5_0,esk7_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k10_yellow_6(esk5_0,esk6_0),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(k10_yellow_6(esk5_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(k10_yellow_6(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k10_yellow_6(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_50]),c_0_13])]),c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(k10_yellow_6(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_48]),c_0_49]),c_0_27])]),c_0_28])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t41_yellow_6, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>r1_tarski(k10_yellow_6(X1,X2),k10_yellow_6(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_yellow_6)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(dt_m2_yellow_6, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>(((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 0.13/0.38  fof(t27_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>![X4]:(r2_waybel_0(X1,X3,X4)=>r2_waybel_0(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_6)).
% 0.13/0.38  fof(t9_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>~(r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_waybel_0)).
% 0.13/0.38  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.13/0.38  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.13/0.38  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m2_yellow_6(X3,X1,X2)=>r1_tarski(k10_yellow_6(X1,X2),k10_yellow_6(X1,X3)))))), inference(assume_negation,[status(cth)],[t41_yellow_6])).
% 0.13/0.38  fof(c_0_9, plain, ![X10]:(~l1_pre_topc(X10)|l1_struct_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((((~v2_struct_0(esk6_0)&v4_orders_2(esk6_0))&v7_waybel_0(esk6_0))&l1_waybel_0(esk6_0,esk5_0))&(m2_yellow_6(esk7_0,esk5_0,esk6_0)&~r1_tarski(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X25, X26, X27]:((((~v2_struct_0(X27)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25)))&(v4_orders_2(X27)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))))&(v7_waybel_0(X27)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))))&(l1_waybel_0(X27,X25)|~m2_yellow_6(X27,X25,X26)|(v2_struct_0(X25)|~l1_struct_0(X25)|v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).
% 0.13/0.38  cnf(c_0_12, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_14, plain, ![X28, X29, X30, X31]:(v2_struct_0(X28)|~l1_struct_0(X28)|(v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28)|(~m2_yellow_6(X30,X28,X29)|(~r2_waybel_0(X28,X30,X31)|r2_waybel_0(X28,X29,X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X11, X12, X13]:((~r1_waybel_0(X11,X12,X13)|~r2_waybel_0(X11,X12,k6_subset_1(u1_struct_0(X11),X13))|(v2_struct_0(X12)|~l1_waybel_0(X12,X11))|(v2_struct_0(X11)|~l1_struct_0(X11)))&(r2_waybel_0(X11,X12,k6_subset_1(u1_struct_0(X11),X13))|r1_waybel_0(X11,X12,X13)|(v2_struct_0(X12)|~l1_waybel_0(X12,X11))|(v2_struct_0(X11)|~l1_struct_0(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (l1_waybel_0(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (m2_yellow_6(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (v7_waybel_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v4_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.38  cnf(c_0_24, plain, (v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(X1)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_25, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_waybel_0(X1,X2,X4)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~m2_yellow_6(X3,X1,X2)|~r2_waybel_0(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_26, plain, (r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (l1_waybel_0(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.38  fof(c_0_29, plain, ![X14, X15, X16, X17, X18, X22]:(((~r2_hidden(X17,X16)|(~m1_connsp_2(X18,X14,X17)|r1_waybel_0(X14,X15,X18))|~m1_subset_1(X17,u1_struct_0(X14))|X16!=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&((m1_connsp_2(esk2_4(X14,X15,X16,X17),X14,X17)|r2_hidden(X17,X16)|~m1_subset_1(X17,u1_struct_0(X14))|X16!=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r1_waybel_0(X14,X15,esk2_4(X14,X15,X16,X17))|r2_hidden(X17,X16)|~m1_subset_1(X17,u1_struct_0(X14))|X16!=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))))&((m1_subset_1(esk3_3(X14,X15,X16),u1_struct_0(X14))|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(((m1_connsp_2(esk4_3(X14,X15,X16),X14,esk3_3(X14,X15,X16))|~r2_hidden(esk3_3(X14,X15,X16),X16)|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r1_waybel_0(X14,X15,esk4_3(X14,X15,X16))|~r2_hidden(esk3_3(X14,X15,X16),X16)|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))))&(r2_hidden(esk3_3(X14,X15,X16),X16)|(~m1_connsp_2(X22,X14,esk3_3(X14,X15,X16))|r1_waybel_0(X14,X15,X22))|X16=k10_yellow_6(X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X15)|~v4_orders_2(X15)|~v7_waybel_0(X15)|~l1_waybel_0(X15,X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.13/0.38  fof(c_0_30, plain, ![X23, X24]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|v2_struct_0(X24)|~v4_orders_2(X24)|~v7_waybel_0(X24)|~l1_waybel_0(X24,X23)|m1_subset_1(k10_yellow_6(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,X1)|~r2_waybel_0(esk5_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (r2_waybel_0(esk5_0,esk7_0,k6_subset_1(u1_struct_0(esk5_0),X1))|r1_waybel_0(esk5_0,esk7_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23])]), c_0_28]), c_0_22])).
% 0.13/0.38  cnf(c_0_33, plain, (v7_waybel_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_34, plain, (v4_orders_2(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m2_yellow_6(X1,X2,X3)|~l1_struct_0(X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_35, plain, (r1_waybel_0(X4,X5,X3)|v2_struct_0(X5)|v2_struct_0(X4)|~r2_hidden(X1,X2)|~m1_connsp_2(X3,X4,X1)|~m1_subset_1(X1,u1_struct_0(X4))|X2!=k10_yellow_6(X4,X5)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))|~v4_orders_2(X5)|~v7_waybel_0(X5)|~l1_waybel_0(X5,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_36, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  fof(c_0_37, plain, ![X6, X7, X8]:((m1_subset_1(esk1_3(X6,X7,X8),X6)|r1_tarski(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X6))|~m1_subset_1(X7,k1_zfmisc_1(X6)))&((r2_hidden(esk1_3(X6,X7,X8),X7)|r1_tarski(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X6))|~m1_subset_1(X7,k1_zfmisc_1(X6)))&(~r2_hidden(esk1_3(X6,X7,X8),X8)|r1_tarski(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X6))|~m1_subset_1(X7,k1_zfmisc_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.13/0.38  cnf(c_0_38, plain, (r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_39, plain, (v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,X3)|~r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,k6_subset_1(u1_struct_0(esk5_0),X1))|r1_waybel_0(esk5_0,esk7_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v7_waybel_0(esk7_0)|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (v4_orders_2(esk7_0)|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.13/0.38  cnf(c_0_43, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X4)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~l1_pre_topc(X1)|~r2_hidden(X4,k10_yellow_6(X1,X2))|~m1_subset_1(X4,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_44, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_45, plain, (m1_connsp_2(esk2_4(X1,X2,X3,X4),X1,X4)|r2_hidden(X4,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|X3!=k10_yellow_6(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_46, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_hidden(X3,k10_yellow_6(X2,X1))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~v2_pre_topc(X2)|~r1_waybel_0(X2,X1,esk2_4(X2,X1,k10_yellow_6(X2,X1),X3))|~l1_waybel_0(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_36])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (r1_waybel_0(esk5_0,esk7_0,X1)|~r1_waybel_0(esk5_0,esk6_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_20]), c_0_23])]), c_0_21]), c_0_22])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (v7_waybel_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_23])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (v4_orders_2(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_23])])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_51, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|r1_tarski(k10_yellow_6(X1,X2),X4)|~m1_connsp_2(X3,X1,esk1_3(X5,k10_yellow_6(X1,X2),X4))|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_3(X5,k10_yellow_6(X1,X2),X4),u1_struct_0(X1))|~m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(X5))|~m1_subset_1(X4,k1_zfmisc_1(X5))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.38  cnf(c_0_52, plain, (m1_connsp_2(esk2_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)|v2_struct_0(X2)|v2_struct_0(X1)|r2_hidden(X3,k10_yellow_6(X1,X2))|~v7_waybel_0(X2)|~v4_orders_2(X2)|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_36])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk5_0,esk7_0))|~r1_waybel_0(esk5_0,esk6_0,esk2_4(esk5_0,esk7_0,k10_yellow_6(esk5_0,esk7_0),X1))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_27]), c_0_13])]), c_0_22]), c_0_28])).
% 0.13/0.38  cnf(c_0_54, plain, (r1_waybel_0(X1,X2,esk2_4(X1,X3,k10_yellow_6(X1,X3),esk1_3(X4,k10_yellow_6(X1,X2),X5)))|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(k10_yellow_6(X1,X2),X5)|r2_hidden(esk1_3(X4,k10_yellow_6(X1,X2),X5),k10_yellow_6(X1,X3))|~v7_waybel_0(X2)|~v7_waybel_0(X3)|~v4_orders_2(X2)|~v4_orders_2(X3)|~v2_pre_topc(X1)|~l1_waybel_0(X2,X1)|~l1_waybel_0(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_3(X4,k10_yellow_6(X1,X2),X5),u1_struct_0(X1))|~m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.38  cnf(c_0_55, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (r1_tarski(k10_yellow_6(esk5_0,esk6_0),X1)|r2_hidden(esk1_3(X2,k10_yellow_6(esk5_0,esk6_0),X1),k10_yellow_6(esk5_0,esk7_0))|~m1_subset_1(esk1_3(X2,k10_yellow_6(esk5_0,esk6_0),X1),u1_struct_0(esk5_0))|~m1_subset_1(k10_yellow_6(esk5_0,esk6_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_18]), c_0_48]), c_0_19]), c_0_49]), c_0_50]), c_0_20]), c_0_27]), c_0_13])]), c_0_28]), c_0_22]), c_0_21])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (~r1_tarski(k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (~m1_subset_1(esk1_3(X1,k10_yellow_6(esk5_0,esk6_0),k10_yellow_6(esk5_0,esk7_0)),u1_struct_0(esk5_0))|~m1_subset_1(k10_yellow_6(esk5_0,esk7_0),k1_zfmisc_1(X1))|~m1_subset_1(k10_yellow_6(esk5_0,esk6_0),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.13/0.38  cnf(c_0_59, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (~m1_subset_1(k10_yellow_6(esk5_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(k10_yellow_6(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_57])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k10_yellow_6(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_50]), c_0_13])]), c_0_22])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (~m1_subset_1(k10_yellow_6(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_48]), c_0_49]), c_0_27])]), c_0_28])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 64
% 0.13/0.38  # Proof object clause steps            : 47
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 30
% 0.13/0.38  # Proof object clause conjectures      : 27
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 24
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 90
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 28
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 92
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 92
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 44
% 0.13/0.38  # ...of the previous two non-trivial   : 42
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 41
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 58
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 5
% 0.13/0.38  #    Non-unit-clauses                  : 43
% 0.13/0.38  # Current number of unprocessed clauses: 6
% 0.13/0.38  # ...number of literals in the above   : 60
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 31
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1226
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 56
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.13/0.38  # Unit Clause-clause subsumption calls : 83
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5896
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.036 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.042 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
