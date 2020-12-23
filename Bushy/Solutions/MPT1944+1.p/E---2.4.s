%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t42_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:56 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 320 expanded)
%              Number of clauses        :   36 ( 103 expanded)
%              Number of leaves         :   10 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  394 (2261 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   81 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',t42_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',d11_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',dt_o_2_6_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',d18_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',dt_k10_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',t25_yellow_6)).

fof(dt_k4_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',dt_k4_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',t6_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t42_yellow_6.p',dt_m1_connsp_2)).

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
    ! [X39] :
      ( ~ l1_pre_topc(X39)
      | l1_struct_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & v7_waybel_0(esk2_0)
    & v1_yellow_6(esk2_0,esk1_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & ~ r2_hidden(k4_yellow_6(esk1_0,esk2_0),k10_yellow_6(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X10,X11,X12,X14,X15,X16] :
      ( ( m1_subset_1(esk3_3(X10,X11,X12),u1_struct_0(X11))
        | ~ r1_waybel_0(X10,X11,X12)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r1_orders_2(X11,esk3_3(X10,X11,X12),X14)
        | r2_hidden(k2_waybel_0(X10,X11,X14),X12)
        | ~ r1_waybel_0(X10,X11,X12)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10) )
      & ( m1_subset_1(esk4_4(X10,X11,X15,X16),u1_struct_0(X11))
        | ~ m1_subset_1(X16,u1_struct_0(X11))
        | r1_waybel_0(X10,X11,X15)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10) )
      & ( r1_orders_2(X11,X16,esk4_4(X10,X11,X15,X16))
        | ~ m1_subset_1(X16,u1_struct_0(X11))
        | r1_waybel_0(X10,X11,X15)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10) )
      & ( ~ r2_hidden(k2_waybel_0(X10,X11,esk4_4(X10,X11,X15,X16)),X15)
        | ~ m1_subset_1(X16,u1_struct_0(X11))
        | r1_waybel_0(X10,X11,X15)
        | v2_struct_0(X11)
        | ~ l1_waybel_0(X11,X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_14,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X45,X46] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | v2_struct_0(X46)
      | ~ v4_orders_2(X46)
      | ~ v7_waybel_0(X46)
      | ~ v1_yellow_6(X46,X45)
      | ~ l1_waybel_0(X46,X45)
      | m1_subset_1(o_2_6_yellow_6(X45,X46),u1_struct_0(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_6_yellow_6])])])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21,X22,X26] :
      ( ( ~ r2_hidden(X21,X20)
        | ~ m1_connsp_2(X22,X18,X21)
        | r1_waybel_0(X18,X19,X22)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | X20 != k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_connsp_2(esk5_4(X18,X19,X20,X21),X18,X21)
        | r2_hidden(X21,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | X20 != k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r1_waybel_0(X18,X19,esk5_4(X18,X19,X20,X21))
        | r2_hidden(X21,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | X20 != k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk6_3(X18,X19,X20),u1_struct_0(X18))
        | X20 = k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_connsp_2(esk7_3(X18,X19,X20),X18,esk6_3(X18,X19,X20))
        | ~ r2_hidden(esk6_3(X18,X19,X20),X20)
        | X20 = k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r1_waybel_0(X18,X19,esk7_3(X18,X19,X20))
        | ~ r2_hidden(esk6_3(X18,X19,X20),X20)
        | X20 = k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk6_3(X18,X19,X20),X20)
        | ~ m1_connsp_2(X26,X18,esk6_3(X18,X19,X20))
        | r1_waybel_0(X18,X19,X26)
        | X20 = k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_18,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ v4_orders_2(X28)
      | ~ v7_waybel_0(X28)
      | ~ l1_waybel_0(X28,X27)
      | m1_subset_1(k10_yellow_6(X27,X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

fof(c_0_19,plain,(
    ! [X65,X66,X67] :
      ( v2_struct_0(X65)
      | ~ l1_struct_0(X65)
      | v2_struct_0(X66)
      | ~ v4_orders_2(X66)
      | ~ v7_waybel_0(X66)
      | ~ v1_yellow_6(X66,X65)
      | ~ l1_waybel_0(X66,X65)
      | ~ m1_subset_1(X67,u1_struct_0(X66))
      | k2_waybel_0(X65,X66,X67) = k4_yellow_6(X65,X66) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_yellow_6])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(o_2_6_yellow_6(X1,X2),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v1_yellow_6(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( m1_connsp_2(esk5_4(X1,X2,X3,X4),X1,X4)
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_32,plain,(
    ! [X36,X37] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | ~ l1_waybel_0(X37,X36)
      | m1_subset_1(k4_yellow_6(X36,X37),u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_yellow_6])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k4_yellow_6(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v1_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_4(esk1_0,esk2_0,X1,X2),u1_struct_0(esk2_0))
    | r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(o_2_6_yellow_6(esk1_0,esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21]),c_0_27]),c_0_28]),c_0_15]),c_0_29])]),c_0_23]),c_0_24])).

fof(c_0_36,plain,(
    ! [X79,X80,X81] :
      ( v2_struct_0(X79)
      | ~ v2_pre_topc(X79)
      | ~ l1_pre_topc(X79)
      | ~ m1_subset_1(X80,k1_zfmisc_1(u1_struct_0(X79)))
      | ~ m1_subset_1(X81,u1_struct_0(X79))
      | ~ m1_connsp_2(X80,X79,X81)
      | r2_hidden(X81,X80) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

fof(c_0_37,plain,(
    ! [X42,X43,X44] :
      ( v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,u1_struct_0(X42))
      | ~ m1_connsp_2(X44,X42,X43)
      | m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_38,plain,
    ( m1_connsp_2(esk5_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_yellow_6(X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k2_waybel_0(esk1_0,esk2_0,X1) = k4_yellow_6(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_22]),c_0_21]),c_0_27]),c_0_28])]),c_0_23]),c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_4(esk1_0,esk2_0,X1,o_2_6_yellow_6(esk1_0,esk2_0)),u1_struct_0(esk2_0))
    | r1_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),X1),esk1_0,X1)
    | r2_hidden(X1,k10_yellow_6(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_27]),c_0_28]),c_0_15]),c_0_29])]),c_0_24]),c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k4_yellow_6(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_21]),c_0_22])]),c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(esk1_0,esk2_0),k10_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( k2_waybel_0(esk1_0,esk2_0,esk4_4(esk1_0,esk2_0,X1,o_2_6_yellow_6(esk1_0,esk2_0))) = k4_yellow_6(esk1_0,esk2_0)
    | r1_waybel_0(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ m1_connsp_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( m1_connsp_2(esk5_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),k4_yellow_6(esk1_0,esk2_0)),esk1_0,k4_yellow_6(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_51,plain,
    ( r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,esk5_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,X1)
    | ~ r2_hidden(k4_yellow_6(esk1_0,esk2_0),X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_22]),c_0_21])]),c_0_23]),c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_yellow_6(esk1_0,esk2_0),esk5_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),k4_yellow_6(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_45]),c_0_15]),c_0_29])]),c_0_24])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_waybel_0(X2,X3,esk5_4(X2,X3,k10_yellow_6(X2,X3),X1))
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk5_4(esk1_0,esk2_0,k10_yellow_6(esk1_0,esk2_0),k4_yellow_6(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_45]),c_0_21]),c_0_27]),c_0_28]),c_0_15]),c_0_29])]),c_0_46]),c_0_24]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
