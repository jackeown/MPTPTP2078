%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2025+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:08 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 504 expanded)
%              Number of clauses        :   56 ( 174 expanded)
%              Number of leaves         :   12 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  509 (4343 expanded)
%              Number of equality atoms :   36 ( 346 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   81 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_9)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d13_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k2_pre_topc(X1,X2)
              <=> ! [X4] :
                    ( r2_hidden(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v3_pre_topc(X5,X1)
                              & r2_hidden(X4,X5)
                              & r1_xboole_0(X2,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).

fof(t8_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
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

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v2_pre_topc(esk8_0)
    & l1_pre_topc(esk8_0)
    & m1_subset_1(esk9_0,u1_struct_0(esk8_0))
    & ~ v2_struct_0(esk10_0)
    & v4_orders_2(esk10_0)
    & v7_waybel_0(esk10_0)
    & l1_waybel_0(esk10_0,esk8_0)
    & r2_hidden(esk9_0,k10_yellow_6(esk8_0,esk10_0))
    & m1_subset_1(esk11_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
    & esk11_0 = k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk10_0))
    & ~ r2_hidden(esk9_0,k2_pre_topc(esk8_0,esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X48,X49,X50] :
      ( ~ r2_hidden(X48,X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(X50))
      | ~ v1_xboole_0(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_waybel_0(esk10_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v7_waybel_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v4_orders_2(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X42,X43)
      | v1_xboole_0(X43)
      | r2_hidden(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k10_yellow_6(esk8_0,esk10_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_23])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,plain,(
    ! [X6,X7,X8,X9,X10,X14] :
      ( ( ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_pre_topc(X10,X6)
        | ~ r2_hidden(X9,X10)
        | ~ r1_xboole_0(X7,X10)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_4(X6,X7,X8,X9),k1_zfmisc_1(u1_struct_0(X6)))
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(esk1_4(X6,X7,X8,X9),X6)
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(X9,esk1_4(X6,X7,X8,X9))
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r1_xboole_0(X7,esk1_4(X6,X7,X8,X9))
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),u1_struct_0(X6))
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk3_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(esk3_3(X6,X7,X8),X6)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),esk3_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r1_xboole_0(X7,esk3_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X8)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_pre_topc(X14,X6)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X14)
        | ~ r1_xboole_0(X7,X14)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).

fof(c_0_30,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | m1_subset_1(k2_pre_topc(X29,X30),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk8_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk8_0))
    | r2_hidden(esk9_0,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk9_0,u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk8_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk9_0,k10_yellow_6(esk8_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,plain,
    ( v3_pre_topc(esk1_4(X1,X2,X3,X4),X1)
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X15,X16,X17,X18,X19,X23] :
      ( ( ~ r2_hidden(X18,X17)
        | ~ m1_connsp_2(X19,X15,X18)
        | r1_waybel_0(X15,X16,X19)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | X17 != k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_connsp_2(esk4_4(X15,X16,X17,X18),X15,X18)
        | r2_hidden(X18,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | X17 != k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r1_waybel_0(X15,X16,esk4_4(X15,X16,X17,X18))
        | r2_hidden(X18,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | X17 != k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk5_3(X15,X16,X17),u1_struct_0(X15))
        | X17 = k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_connsp_2(esk6_3(X15,X16,X17),X15,esk5_3(X15,X16,X17))
        | ~ r2_hidden(esk5_3(X15,X16,X17),X17)
        | X17 = k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r1_waybel_0(X15,X16,esk6_3(X15,X16,X17))
        | ~ r2_hidden(esk5_3(X15,X16,X17),X17)
        | X17 = k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk5_3(X15,X16,X17),X17)
        | ~ m1_connsp_2(X23,X15,esk5_3(X15,X16,X17))
        | r1_waybel_0(X15,X16,X23)
        | X17 = k10_yellow_6(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X16)
        | ~ v4_orders_2(X16)
        | ~ v7_waybel_0(X16)
        | ~ l1_waybel_0(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_39,plain,(
    ! [X44,X45,X46,X47] :
      ( ( ~ v3_pre_topc(X47,X45)
        | k1_tops_1(X45,X47) = X47
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X45)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( k1_tops_1(X44,X46) != X46
        | v3_pre_topc(X46,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X45)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,X3))
    | m1_subset_1(esk1_4(X2,X3,k2_pre_topc(X2,X3),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk9_0,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( v3_pre_topc(esk1_4(X1,X2,k2_pre_topc(X1,X2),X3),X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,esk1_4(X2,X3,X4,X1))
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | X4 != k2_pre_topc(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_45,plain,(
    ! [X24,X25,X26] :
      ( ( ~ m1_connsp_2(X26,X24,X25)
        | r2_hidden(X25,k1_tops_1(X24,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ r2_hidden(X25,k1_tops_1(X24,X26))
        | m1_connsp_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_46,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk9_0,k2_pre_topc(esk8_0,X1))
    | m1_subset_1(esk1_4(esk8_0,X1,k2_pre_topc(esk8_0,X1),esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_21])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k2_pre_topc(esk8_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(esk1_4(esk8_0,X1,k2_pre_topc(esk8_0,X1),esk9_0),esk8_0)
    | r2_hidden(esk9_0,k2_pre_topc(esk8_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_21])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,esk1_4(X2,X3,k2_pre_topc(X2,X3),X1))
    | r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_34])).

cnf(c_0_52,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X4,k10_yellow_6(X1,X2))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_16])).

cnf(c_0_53,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_20]),c_0_21])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_47]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk9_0,esk1_4(esk8_0,X1,k2_pre_topc(esk8_0,X1),esk9_0))
    | r2_hidden(esk9_0,k2_pre_topc(esk8_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_41]),c_0_21])])).

cnf(c_0_58,negated_conjecture,
    ( r1_waybel_0(esk8_0,X1,X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X2,esk8_0,esk9_0)
    | ~ l1_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ r2_hidden(esk9_0,k10_yellow_6(esk8_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_28]),c_0_20]),c_0_21])]),c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( m1_connsp_2(X1,esk8_0,esk9_0)
    | ~ r2_hidden(esk9_0,k1_tops_1(esk8_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_28]),c_0_20]),c_0_21])]),c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( k1_tops_1(esk8_0,esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0)) = esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_21])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk9_0,esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_47]),c_0_49])).

fof(c_0_62,plain,(
    ! [X38,X39,X40,X41] :
      ( v2_struct_0(X38)
      | ~ l1_struct_0(X38)
      | v2_struct_0(X39)
      | ~ v4_orders_2(X39)
      | ~ v7_waybel_0(X39)
      | ~ l1_waybel_0(X39,X38)
      | ~ r1_waybel_0(X38,X39,X40)
      | ~ r1_waybel_0(X38,X39,X41)
      | ~ r1_xboole_0(X40,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_yellow_6])])])])).

cnf(c_0_63,negated_conjecture,
    ( r1_waybel_0(esk8_0,esk10_0,X1)
    | ~ m1_connsp_2(X1,esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_17]),c_0_18]),c_0_19]),c_0_36])]),c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( m1_connsp_2(esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0),esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_55])])).

fof(c_0_65,plain,(
    ! [X51,X52] :
      ( v2_struct_0(X51)
      | ~ l1_struct_0(X51)
      | v2_struct_0(X52)
      | ~ l1_waybel_0(X52,X51)
      | r1_waybel_0(X51,X52,k2_relset_1(u1_struct_0(X52),u1_struct_0(X51),u1_waybel_0(X51,X52))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_9])])])])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,esk1_4(X2,X1,X3,X4))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X2))
    | X3 != k2_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r1_waybel_0(X1,X2,X4)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r1_waybel_0(esk8_0,esk10_0,esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_69,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( esk11_0 = k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,esk1_4(X2,X1,k2_pre_topc(X2,X1),X3))
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_34])).

cnf(c_0_73,negated_conjecture,
    ( ~ l1_struct_0(esk8_0)
    | ~ r1_waybel_0(esk8_0,esk10_0,X1)
    | ~ r1_xboole_0(X1,esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_17]),c_0_18]),c_0_19])]),c_0_22]),c_0_23])).

cnf(c_0_74,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( r1_waybel_0(esk8_0,esk10_0,esk11_0)
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_17]),c_0_71]),c_0_22]),c_0_23])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(X1,esk1_4(esk8_0,X1,k2_pre_topc(esk8_0,X1),esk9_0))
    | r2_hidden(esk9_0,k2_pre_topc(esk8_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_41]),c_0_21])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_waybel_0(esk8_0,esk10_0,X1)
    | ~ r1_xboole_0(X1,esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_21])])).

cnf(c_0_78,negated_conjecture,
    ( r1_waybel_0(esk8_0,esk10_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_74]),c_0_21])])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(esk11_0,esk1_4(esk8_0,esk11_0,k2_pre_topc(esk8_0,esk11_0),esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_47]),c_0_49])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])]),
    [proof]).

%------------------------------------------------------------------------------
