%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:42 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 173 expanded)
%              Number of clauses        :   36 (  57 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  385 (1607 expanded)
%              Number of equality atoms :   13 ( 101 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   81 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

fof(t24_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v4_orders_2(X3)
                & v7_waybel_0(X3)
                & l1_waybel_0(X3,X1) )
             => ( r2_hidden(X2,k10_yellow_6(X1,X3))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = k2_relset_1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3))
                     => r2_hidden(X2,k2_pre_topc(X1,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_9)).

fof(t39_tops_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ~ ( v3_pre_topc(X4,X1)
                        & r2_hidden(X3,X4)
                        & r1_xboole_0(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tops_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t26_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ~ ( r1_waybel_0(X1,X2,X3)
                & r1_waybel_0(X1,X2,X4)
                & r1_xboole_0(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_6)).

fof(t8_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

fof(c_0_9,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | ~ v3_pre_topc(X16,X15)
      | ~ r2_hidden(X17,X16)
      | m1_connsp_2(X16,X15,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_10,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_11,plain,(
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
      & ( m1_connsp_2(esk2_4(X18,X19,X20,X21),X18,X21)
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
      & ( ~ r1_waybel_0(X18,X19,esk2_4(X18,X19,X20,X21))
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
      & ( m1_subset_1(esk3_3(X18,X19,X20),u1_struct_0(X18))
        | X20 = k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_connsp_2(esk4_3(X18,X19,X20),X18,esk3_3(X18,X19,X20))
        | ~ r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r1_waybel_0(X18,X19,esk4_3(X18,X19,X20))
        | ~ r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k10_yellow_6(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ v4_orders_2(X19)
        | ~ v7_waybel_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk3_3(X18,X19,X20),X20)
        | ~ m1_connsp_2(X26,X18,esk3_3(X18,X19,X20))
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

fof(c_0_12,plain,(
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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v4_orders_2(X3)
                  & v7_waybel_0(X3)
                  & l1_waybel_0(X3,X1) )
               => ( r2_hidden(X2,k10_yellow_6(X1,X3))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X4 = k2_relset_1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3))
                       => r2_hidden(X2,k2_pre_topc(X1,X4)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_waybel_9])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v3_pre_topc(X13,X10)
        | ~ r2_hidden(X12,X13)
        | ~ r1_xboole_0(X11,X13)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X12),k1_zfmisc_1(u1_struct_0(X10)))
        | r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v3_pre_topc(esk1_3(X10,X11,X12),X10)
        | r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(X12,esk1_3(X10,X11,X12))
        | r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r1_xboole_0(X11,esk1_3(X10,X11,X12))
        | r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_tops_1])])])])])])).

cnf(c_0_17,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ~ v2_struct_0(esk7_0)
    & v4_orders_2(esk7_0)
    & v7_waybel_0(esk7_0)
    & l1_waybel_0(esk7_0,esk5_0)
    & r2_hidden(esk6_0,k10_yellow_6(esk5_0,esk7_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & esk8_0 = k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0))
    & ~ r2_hidden(esk6_0,k2_pre_topc(esk5_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_20,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_connsp_2(X3,X1,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X4,k10_yellow_6(X1,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_17,c_0_15])]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk6_0,k10_yellow_6(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v7_waybel_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( m1_connsp_2(esk1_3(X1,X2,X3),X1,X4)
    | v2_struct_0(X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X4,esk1_3(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | r2_hidden(X1,k2_pre_topc(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_34,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_35,plain,(
    ! [X29,X30,X31,X32] :
      ( v2_struct_0(X29)
      | ~ l1_struct_0(X29)
      | v2_struct_0(X30)
      | ~ v4_orders_2(X30)
      | ~ v7_waybel_0(X30)
      | ~ l1_waybel_0(X30,X29)
      | ~ r1_waybel_0(X29,X30,X31)
      | ~ r1_waybel_0(X29,X30,X32)
      | ~ r1_xboole_0(X31,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_yellow_6])])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk7_0,X1)
    | ~ m1_connsp_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_37,plain,
    ( m1_connsp_2(esk1_3(X1,X2,X3),X1,X3)
    | v2_struct_0(X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r1_waybel_0(X1,X2,X4)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk7_0,esk1_3(esk5_0,X1,esk6_0))
    | r2_hidden(esk6_0,k2_pre_topc(esk5_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28]),c_0_29]),c_0_38])]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_pre_topc(esk5_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( esk8_0 = k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk5_0,X1))
    | ~ r1_waybel_0(esk5_0,esk7_0,X2)
    | ~ r1_xboole_0(X2,esk1_3(esk5_0,X1,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_25]),c_0_26]),c_0_27]),c_0_42])]),c_0_31]),c_0_30])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,esk1_3(X2,X1,X3))
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_pre_topc(esk5_0,k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0)))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk5_0,X1))
    | ~ r1_waybel_0(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_28]),c_0_29]),c_0_38])]),c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_44])).

fof(c_0_51,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ l1_struct_0(X33)
      | v2_struct_0(X34)
      | ~ l1_waybel_0(X34,X33)
      | r1_waybel_0(X33,X34,k2_relset_1(u1_struct_0(X34),u1_struct_0(X33),u1_waybel_0(X33,X34))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_9])])])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_waybel_0(esk5_0,esk7_0,k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_25]),c_0_42])]),c_0_31]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:35:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.21/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.028 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.21/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.38  fof(d18_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k10_yellow_6(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)<=>![X5]:(m1_connsp_2(X5,X1,X4)=>r1_waybel_0(X1,X2,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 0.21/0.38  fof(dt_k10_yellow_6, axiom, ![X1, X2]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 0.21/0.38  fof(t24_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(r2_hidden(X2,k10_yellow_6(X1,X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=k2_relset_1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3))=>r2_hidden(X2,k2_pre_topc(X1,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_waybel_9)).
% 0.21/0.38  fof(t39_tops_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_tops_1)).
% 0.21/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.38  fof(t26_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:~(((r1_waybel_0(X1,X2,X3)&r1_waybel_0(X1,X2,X4))&r1_xboole_0(X3,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_6)).
% 0.21/0.38  fof(t8_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_9)).
% 0.21/0.38  fof(c_0_9, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(~m1_subset_1(X17,u1_struct_0(X15))|(~v3_pre_topc(X16,X15)|~r2_hidden(X17,X16)|m1_connsp_2(X16,X15,X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.21/0.38  fof(c_0_10, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.38  fof(c_0_11, plain, ![X18, X19, X20, X21, X22, X26]:(((~r2_hidden(X21,X20)|(~m1_connsp_2(X22,X18,X21)|r1_waybel_0(X18,X19,X22))|~m1_subset_1(X21,u1_struct_0(X18))|X20!=k10_yellow_6(X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X19)|~v4_orders_2(X19)|~v7_waybel_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&((m1_connsp_2(esk2_4(X18,X19,X20,X21),X18,X21)|r2_hidden(X21,X20)|~m1_subset_1(X21,u1_struct_0(X18))|X20!=k10_yellow_6(X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X19)|~v4_orders_2(X19)|~v7_waybel_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~r1_waybel_0(X18,X19,esk2_4(X18,X19,X20,X21))|r2_hidden(X21,X20)|~m1_subset_1(X21,u1_struct_0(X18))|X20!=k10_yellow_6(X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X19)|~v4_orders_2(X19)|~v7_waybel_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))))&((m1_subset_1(esk3_3(X18,X19,X20),u1_struct_0(X18))|X20=k10_yellow_6(X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X19)|~v4_orders_2(X19)|~v7_waybel_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(((m1_connsp_2(esk4_3(X18,X19,X20),X18,esk3_3(X18,X19,X20))|~r2_hidden(esk3_3(X18,X19,X20),X20)|X20=k10_yellow_6(X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X19)|~v4_orders_2(X19)|~v7_waybel_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~r1_waybel_0(X18,X19,esk4_3(X18,X19,X20))|~r2_hidden(esk3_3(X18,X19,X20),X20)|X20=k10_yellow_6(X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X19)|~v4_orders_2(X19)|~v7_waybel_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))))&(r2_hidden(esk3_3(X18,X19,X20),X20)|(~m1_connsp_2(X26,X18,esk3_3(X18,X19,X20))|r1_waybel_0(X18,X19,X26))|X20=k10_yellow_6(X18,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X19)|~v4_orders_2(X19)|~v7_waybel_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).
% 0.21/0.38  fof(c_0_12, plain, ![X27, X28]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27)|m1_subset_1(k10_yellow_6(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_yellow_6])])])).
% 0.21/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(r2_hidden(X2,k10_yellow_6(X1,X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=k2_relset_1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3))=>r2_hidden(X2,k2_pre_topc(X1,X4))))))))), inference(assume_negation,[status(cth)],[t24_waybel_9])).
% 0.21/0.38  cnf(c_0_14, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_15, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  fof(c_0_16, plain, ![X10, X11, X12, X13]:((~r2_hidden(X12,k2_pre_topc(X10,X11))|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))|(~v3_pre_topc(X13,X10)|~r2_hidden(X12,X13)|~r1_xboole_0(X11,X13)))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&((m1_subset_1(esk1_3(X10,X11,X12),k1_zfmisc_1(u1_struct_0(X10)))|r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(((v3_pre_topc(esk1_3(X10,X11,X12),X10)|r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(r2_hidden(X12,esk1_3(X10,X11,X12))|r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(r1_xboole_0(X11,esk1_3(X10,X11,X12))|r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_tops_1])])])])])])).
% 0.21/0.38  cnf(c_0_17, plain, (r1_waybel_0(X4,X5,X3)|v2_struct_0(X5)|v2_struct_0(X4)|~r2_hidden(X1,X2)|~m1_connsp_2(X3,X4,X1)|~m1_subset_1(X1,u1_struct_0(X4))|X2!=k10_yellow_6(X4,X5)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))|~v4_orders_2(X5)|~v7_waybel_0(X5)|~l1_waybel_0(X5,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_18, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  fof(c_0_19, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&((((~v2_struct_0(esk7_0)&v4_orders_2(esk7_0))&v7_waybel_0(esk7_0))&l1_waybel_0(esk7_0,esk5_0))&(r2_hidden(esk6_0,k10_yellow_6(esk5_0,esk7_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(esk8_0=k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0))&~r2_hidden(esk6_0,k2_pre_topc(esk5_0,esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.21/0.38  cnf(c_0_20, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.38  cnf(c_0_21, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|r2_hidden(X3,k2_pre_topc(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  cnf(c_0_22, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|r2_hidden(X3,k2_pre_topc(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  cnf(c_0_23, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~m1_connsp_2(X3,X1,X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X4,k10_yellow_6(X1,X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_17, c_0_15])]), c_0_18])).
% 0.21/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk6_0,k10_yellow_6(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (l1_waybel_0(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, (v7_waybel_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (v4_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_32, plain, (m1_connsp_2(esk1_3(X1,X2,X3),X1,X4)|v2_struct_0(X1)|r2_hidden(X3,k2_pre_topc(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X4,esk1_3(X1,X2,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.21/0.38  cnf(c_0_33, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|r2_hidden(X1,k2_pre_topc(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  fof(c_0_34, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.38  fof(c_0_35, plain, ![X29, X30, X31, X32]:(v2_struct_0(X29)|~l1_struct_0(X29)|(v2_struct_0(X30)|~v4_orders_2(X30)|~v7_waybel_0(X30)|~l1_waybel_0(X30,X29)|(~r1_waybel_0(X29,X30,X31)|~r1_waybel_0(X29,X30,X32)|~r1_xboole_0(X31,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_yellow_6])])])])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (r1_waybel_0(esk5_0,esk7_0,X1)|~m1_connsp_2(X1,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30]), c_0_31])).
% 0.21/0.38  cnf(c_0_37, plain, (m1_connsp_2(esk1_3(X1,X2,X3),X1,X3)|v2_struct_0(X1)|r2_hidden(X3,k2_pre_topc(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_39, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.38  cnf(c_0_40, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~r1_waybel_0(X1,X2,X3)|~r1_waybel_0(X1,X2,X4)|~r1_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.38  cnf(c_0_41, negated_conjecture, (r1_waybel_0(esk5_0,esk7_0,esk1_3(esk5_0,X1,esk6_0))|r2_hidden(esk6_0,k2_pre_topc(esk5_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_28]), c_0_29]), c_0_38])]), c_0_30])).
% 0.21/0.38  cnf(c_0_42, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_29])).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk6_0,k2_pre_topc(esk5_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, (esk8_0=k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk5_0,X1))|~r1_waybel_0(esk5_0,esk7_0,X2)|~r1_xboole_0(X2,esk1_3(esk5_0,X1,esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_25]), c_0_26]), c_0_27]), c_0_42])]), c_0_31]), c_0_30])).
% 0.21/0.38  cnf(c_0_46, plain, (r1_xboole_0(X1,esk1_3(X2,X1,X3))|r2_hidden(X3,k2_pre_topc(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk6_0,k2_pre_topc(esk5_0,k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0))))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk5_0,X1))|~r1_waybel_0(esk5_0,esk7_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_28]), c_0_29]), c_0_38])]), c_0_30])).
% 0.21/0.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_47, c_0_44])).
% 0.21/0.38  fof(c_0_51, plain, ![X33, X34]:(v2_struct_0(X33)|~l1_struct_0(X33)|(v2_struct_0(X34)|~l1_waybel_0(X34,X33)|r1_waybel_0(X33,X34,k2_relset_1(u1_struct_0(X34),u1_struct_0(X33),u1_waybel_0(X33,X34))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_9])])])])).
% 0.21/0.38  cnf(c_0_52, negated_conjecture, (~r1_waybel_0(esk5_0,esk7_0,k2_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),u1_waybel_0(esk5_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.21/0.38  cnf(c_0_53, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_25]), c_0_42])]), c_0_31]), c_0_30]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 55
% 0.21/0.38  # Proof object clause steps            : 36
% 0.21/0.38  # Proof object formula steps           : 19
% 0.21/0.38  # Proof object conjectures             : 24
% 0.21/0.38  # Proof object clause conjectures      : 21
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 23
% 0.21/0.38  # Proof object initial formulas used   : 9
% 0.21/0.38  # Proof object generating inferences   : 9
% 0.21/0.38  # Proof object simplifying inferences  : 39
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 9
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 30
% 0.21/0.38  # Removed in clause preprocessing      : 0
% 0.21/0.38  # Initial clauses in saturation        : 30
% 0.21/0.38  # Processed clauses                    : 89
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 89
% 0.21/0.38  # Other redundant clauses eliminated   : 3
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 2
% 0.21/0.38  # Generated clauses                    : 35
% 0.21/0.38  # ...of the previous two non-trivial   : 31
% 0.21/0.38  # Contextual simplify-reflections      : 10
% 0.21/0.38  # Paramodulations                      : 32
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 3
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 54
% 0.21/0.38  #    Positive orientable unit clauses  : 10
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 4
% 0.21/0.38  #    Non-unit-clauses                  : 40
% 0.21/0.38  # Current number of unprocessed clauses: 2
% 0.21/0.38  # ...number of literals in the above   : 31
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 32
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 820
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 52
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.21/0.38  # Unit Clause-clause subsumption calls : 4
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 1
% 0.21/0.38  # BW rewrite match successes           : 1
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 5949
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.034 s
% 0.21/0.38  # System time              : 0.007 s
% 0.21/0.38  # Total time               : 0.041 s
% 0.21/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
