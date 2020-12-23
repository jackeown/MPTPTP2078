%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_9__t29_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:09 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 141 expanded)
%              Number of clauses        :   25 (  43 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  285 (1147 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   81 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_waybel_9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',t29_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',d9_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',d18_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',dt_k10_yellow_6)).

fof(t28_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
             => r2_waybel_0(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',t28_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t29_waybel_9.p',dt_l1_pre_topc)).

fof(c_0_7,negated_conjecture,(
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
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k10_yellow_6(X1,X2))
                 => r3_waybel_9(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_waybel_9])).

fof(c_0_8,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ r3_waybel_9(X20,X21,X22)
        | ~ m1_connsp_2(X23,X20,X22)
        | r2_waybel_0(X20,X21,X23)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_connsp_2(esk7_3(X20,X21,X22),X20,X22)
        | r3_waybel_9(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_waybel_0(X20,X21,esk7_3(X20,X21,X22))
        | r3_waybel_9(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & v7_waybel_0(esk2_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0))
    & ~ r3_waybel_9(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14,X15,X19] :
      ( ( ~ r2_hidden(X14,X13)
        | ~ m1_connsp_2(X15,X11,X14)
        | r1_waybel_0(X11,X12,X15)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | X13 != k10_yellow_6(X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_connsp_2(esk4_4(X11,X12,X13,X14),X11,X14)
        | r2_hidden(X14,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | X13 != k10_yellow_6(X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r1_waybel_0(X11,X12,esk4_4(X11,X12,X13,X14))
        | r2_hidden(X14,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | X13 != k10_yellow_6(X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk5_3(X11,X12,X13),u1_struct_0(X11))
        | X13 = k10_yellow_6(X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_connsp_2(esk6_3(X11,X12,X13),X11,esk5_3(X11,X12,X13))
        | ~ r2_hidden(esk5_3(X11,X12,X13),X13)
        | X13 = k10_yellow_6(X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r1_waybel_0(X11,X12,esk6_3(X11,X12,X13))
        | ~ r2_hidden(esk5_3(X11,X12,X13),X13)
        | X13 = k10_yellow_6(X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk5_3(X11,X12,X13),X13)
        | ~ m1_connsp_2(X19,X11,esk5_3(X11,X12,X13))
        | r1_waybel_0(X11,X12,X19)
        | X13 = k10_yellow_6(X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_11,plain,(
    ! [X53,X54,X55] :
      ( ~ r2_hidden(X53,X54)
      | ~ m1_subset_1(X54,k1_zfmisc_1(X55))
      | m1_subset_1(X53,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ v4_orders_2(X26)
      | ~ v7_waybel_0(X26)
      | ~ l1_waybel_0(X26,X25)
      | m1_subset_1(k10_yellow_6(X25,X26),k1_zfmisc_1(u1_struct_0(X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).

cnf(c_0_13,plain,
    ( m1_connsp_2(esk7_3(X1,X2,X3),X1,X3)
    | r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( m1_connsp_2(esk7_3(esk1_0,esk2_0,X1),esk1_0,X1)
    | r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X4)
    | ~ r2_hidden(X4,k10_yellow_6(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_19,c_0_20])]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_connsp_2(esk7_3(esk1_0,esk2_0,esk3_0),esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_27,plain,(
    ! [X46,X47,X48] :
      ( v2_struct_0(X46)
      | ~ l1_struct_0(X46)
      | v2_struct_0(X47)
      | ~ v4_orders_2(X47)
      | ~ v7_waybel_0(X47)
      | ~ l1_waybel_0(X47,X46)
      | ~ r1_waybel_0(X46,X47,X48)
      | r2_waybel_0(X46,X47,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_yellow_6])])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_waybel_0(esk1_0,X1,esk7_3(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r2_hidden(esk3_0,k10_yellow_6(esk1_0,X1))
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_15]),c_0_16])]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_0,k10_yellow_6(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r1_waybel_0(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_29]),c_0_30]),c_0_31])]),c_0_17])).

fof(c_0_34,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_14]),c_0_30]),c_0_31])]),c_0_17]),c_0_18])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,esk7_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23]),c_0_14]),c_0_15]),c_0_16])]),c_0_24]),c_0_17]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
