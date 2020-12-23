%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1944+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 435 expanded)
%              Number of clauses        :   41 ( 137 expanded)
%              Number of leaves         :   10 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  469 (3172 expanded)
%              Number of equality atoms :   17 (  43 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   81 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v1_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).

fof(t25_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v1_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => k2_waybel_0(X1,X2,X3) = k4_yellow_6(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_o_2_6_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & v1_yellow_6(X2,X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(o_2_6_yellow_6(X1,X2),u1_struct_0(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_6_yellow_6)).

fof(d11_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ? [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( r1_orders_2(X2,X4,X5)
                       => r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(t6_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( m1_connsp_2(X2,X1,X3)
               => r2_hidden(X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

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

fof(dt_k4_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & v1_yellow_6(X2,X1)
              & l1_waybel_0(X2,X1) )
           => r2_hidden(k4_yellow_6(X1,X2),k10_yellow_6(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t42_yellow_6])).

fof(c_0_11,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ l1_struct_0(X33)
      | v2_struct_0(X34)
      | ~ v4_orders_2(X34)
      | ~ v7_waybel_0(X34)
      | ~ v1_yellow_6(X34,X33)
      | ~ l1_waybel_0(X34,X33)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | k2_waybel_0(X33,X34,X35) = k4_yellow_6(X33,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow_6])])])])).

fof(c_0_12,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | l1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & v4_orders_2(esk7_0)
    & v7_waybel_0(esk7_0)
    & v1_yellow_6(esk7_0,esk6_0)
    & l1_waybel_0(esk7_0,esk6_0)
    & ~ r2_hidden(k4_yellow_6(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k4_yellow_6(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_waybel_0(X1,X2,X3) = k2_waybel_0(X1,X2,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_yellow_6(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v7_waybel_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ v4_orders_2(X32)
      | ~ v7_waybel_0(X32)
      | ~ v1_yellow_6(X32,X31)
      | ~ l1_waybel_0(X32,X31)
      | m1_subset_1(o_2_6_yellow_6(X31,X32),u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_6_yellow_6])])])).

fof(c_0_26,plain,(
    ! [X6,X7,X8,X10,X11,X12] :
      ( ( m1_subset_1(esk1_3(X6,X7,X8),u1_struct_0(X7))
        | ~ r1_waybel_0(X6,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,esk1_3(X6,X7,X8),X10)
        | r2_hidden(k2_waybel_0(X6,X7,X10),X8)
        | ~ r1_waybel_0(X6,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( m1_subset_1(esk2_4(X6,X7,X11,X12),u1_struct_0(X7))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,X11)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( r1_orders_2(X7,X12,esk2_4(X6,X7,X11,X12))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,X11)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( ~ r2_hidden(k2_waybel_0(X6,X7,esk2_4(X6,X7,X11,X12)),X11)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,X11)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( k2_waybel_0(esk6_0,esk7_0,X1) = k2_waybel_0(esk6_0,esk7_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(o_2_6_yellow_6(X1,X2),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk2_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k2_waybel_0(esk6_0,esk7_0,X1) = k4_yellow_6(esk6_0,esk7_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_27]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_24]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(o_2_6_yellow_6(esk6_0,esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_19]),c_0_20]),c_0_16]),c_0_29]),c_0_21])]),c_0_24]),c_0_23])).

fof(c_0_34,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | ~ m1_connsp_2(X37,X36,X38)
      | r2_hidden(X38,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

fof(c_0_35,plain,(
    ! [X28,X29,X30] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_connsp_2(X30,X28,X29)
      | m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_36,plain,(
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
      & ( m1_connsp_2(esk3_4(X14,X15,X16,X17),X14,X17)
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
      & ( ~ r1_waybel_0(X14,X15,esk3_4(X14,X15,X16,X17))
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
      & ( m1_subset_1(esk4_3(X14,X15,X16),u1_struct_0(X14))
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_connsp_2(esk5_3(X14,X15,X16),X14,esk4_3(X14,X15,X16))
        | ~ r2_hidden(esk4_3(X14,X15,X16),X16)
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r1_waybel_0(X14,X15,esk5_3(X14,X15,X16))
        | ~ r2_hidden(esk4_3(X14,X15,X16),X16)
        | X16 = k10_yellow_6(X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X15)
        | ~ v4_orders_2(X15)
        | ~ v7_waybel_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk4_3(X14,X15,X16),X16)
        | ~ m1_connsp_2(X22,X14,esk4_3(X14,X15,X16))
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

fof(c_0_37,plain,(
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

cnf(c_0_38,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r2_hidden(k4_yellow_6(X1,X2),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k2_waybel_0(esk6_0,esk7_0,X1) = k4_yellow_6(esk6_0,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( m1_connsp_2(esk3_4(X1,X2,X3,X4),X1,X4)
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
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | ~ l1_waybel_0(X26,X25)
      | m1_subset_1(k4_yellow_6(X25,X26),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).

cnf(c_0_45,negated_conjecture,
    ( r1_waybel_0(esk6_0,esk7_0,X1)
    | ~ r2_hidden(k2_waybel_0(esk6_0,esk7_0,X2),X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ m1_connsp_2(X2,X3,X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( m1_connsp_2(esk3_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_43])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_waybel_0(esk6_0,esk7_0,X1)
    | ~ r2_hidden(k4_yellow_6(esk6_0,esk7_0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_14]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_24]),c_0_23])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,esk3_4(X2,X3,k10_yellow_6(X2,X3),X1))
    | r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_waybel_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( m1_subset_1(k2_waybel_0(X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_yellow_6(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk6_0,esk7_0),k10_yellow_6(X1,X2))
    | r1_waybel_0(esk6_0,esk7_0,esk3_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k4_yellow_6(esk6_0,esk7_0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk7_0))
    | ~ l1_waybel_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_waybel_0(esk6_0,esk7_0,X1),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_24]),c_0_23])).

cnf(c_0_54,plain,
    ( r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk6_0,esk7_0),k10_yellow_6(X1,X2))
    | r1_waybel_0(esk6_0,esk7_0,esk3_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk6_0,esk7_0)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k4_yellow_6(esk6_0,esk7_0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(esk7_0))
    | ~ l1_waybel_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_33])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k4_yellow_6(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_14]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_24]),c_0_23])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_waybel_0(X2,X3,esk3_4(X2,X3,k10_yellow_6(X2,X3),X1))
    | ~ l1_waybel_0(X3,X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk6_0,esk7_0),k10_yellow_6(X1,X2))
    | r1_waybel_0(esk6_0,esk7_0,esk3_4(X1,X2,k10_yellow_6(X1,X2),k4_yellow_6(esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k4_yellow_6(esk6_0,esk7_0),u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_33])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k4_yellow_6(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_33])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(esk6_0,esk7_0),k10_yellow_6(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_19]),c_0_20]),c_0_16]),c_0_29]),c_0_59]),c_0_21])]),c_0_60]),c_0_23]),c_0_24]),
    [proof]).

%------------------------------------------------------------------------------
