%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2054+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:10 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :  106 (11151 expanded)
%              Number of clauses        :   77 (3708 expanded)
%              Number of leaves         :   14 (2693 expanded)
%              Depth                    :   30
%              Number of atoms          :  581 (97827 expanded)
%              Number of equality atoms :   11 (1251 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   81 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t13_yellow19,conjecture,(
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
              <=> r2_waybel_7(X1,k2_yellow19(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).

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

fof(d5_waybel_7,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( r2_waybel_7(X1,X2,X3)
        <=> ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X4,X1)
                  & r2_hidden(X3,X4) )
               => r2_hidden(X4,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).

fof(t11_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_hidden(X3,k2_yellow19(X1,X2))
            <=> ( r1_waybel_0(X1,X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ( r1_tarski(X3,X4)
             => ( ( r1_waybel_0(X1,X2,X3)
                 => r1_waybel_0(X1,X2,X4) )
                & ( r2_waybel_0(X1,X2,X3)
                 => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9,X10,X14] :
      ( ( ~ r2_hidden(X9,X8)
        | ~ m1_connsp_2(X10,X6,X9)
        | r1_waybel_0(X6,X7,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_connsp_2(esk1_4(X6,X7,X8,X9),X6,X9)
        | r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ r1_waybel_0(X6,X7,esk1_4(X6,X7,X8,X9))
        | r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X8),u1_struct_0(X6))
        | X8 = k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_connsp_2(esk3_3(X6,X7,X8),X6,esk2_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ r1_waybel_0(X6,X7,esk3_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X8)
        | ~ m1_connsp_2(X14,X6,esk2_3(X6,X7,X8))
        | r1_waybel_0(X6,X7,X14)
        | X8 = k10_yellow_6(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_yellow_6])])])])])])).

fof(c_0_15,plain,(
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

fof(c_0_16,negated_conjecture,(
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
                <=> r2_waybel_7(X1,k2_yellow19(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow19])).

cnf(c_0_17,plain,
    ( m1_connsp_2(esk1_4(X1,X2,X3,X4),X1,X4)
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_yellow_6(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v4_orders_2(esk6_0)
    & v7_waybel_0(esk6_0)
    & l1_waybel_0(esk6_0,esk5_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & ( ~ r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0))
      | ~ r2_waybel_7(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0) )
    & ( r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0))
      | r2_waybel_7(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_20,plain,(
    ! [X30,X31,X32] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ m1_connsp_2(X32,X30,X31)
      | m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_21,plain,
    ( m1_connsp_2(esk1_4(X1,X2,k10_yellow_6(X1,X2),X3),X1,X3)
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_connsp_2(esk1_4(esk5_0,X1,k10_yellow_6(esk5_0,X1),esk7_0),esk5_0,esk7_0)
    | r2_hidden(esk7_0,k10_yellow_6(esk5_0,X1))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v7_waybel_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_connsp_2(X1,esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_connsp_2(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),esk5_0,esk7_0)
    | r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_34,plain,(
    ! [X43,X44,X45] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | ~ m1_subset_1(X45,u1_struct_0(X43))
      | ~ v3_pre_topc(X44,X43)
      | ~ r2_hidden(X45,X44)
      | m1_connsp_2(X44,X43,X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_35,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | m1_subset_1(X40,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0))
    | ~ r2_waybel_7(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0))
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_waybel_7(X18,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v3_pre_topc(X21,X18)
        | ~ r2_hidden(X20,X21)
        | r2_hidden(X21,X19)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk4_3(X18,X22,X23),k1_zfmisc_1(u1_struct_0(X18)))
        | r2_waybel_7(X18,X22,X23)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( v3_pre_topc(esk4_3(X18,X22,X23),X18)
        | r2_waybel_7(X18,X22,X23)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(X23,esk4_3(X18,X22,X23))
        | r2_waybel_7(X18,X22,X23)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r2_hidden(esk4_3(X18,X22,X23),X22)
        | r2_waybel_7(X18,X22,X23)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_waybel_7(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | m1_subset_1(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_23]),c_0_24])])).

fof(c_0_45,plain,(
    ! [X35,X36,X37] :
      ( ( r1_waybel_0(X35,X36,X37)
        | ~ r2_hidden(X37,k2_yellow19(X35,X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ r2_hidden(X37,k2_yellow19(X35,X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( ~ r1_waybel_0(X35,X36,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | r2_hidden(X37,k2_yellow19(X35,X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t11_yellow19])])])])])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( m1_connsp_2(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),esk5_0,X1)
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v3_pre_topc(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),esk5_0)
    | ~ r2_hidden(X1,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_48,plain,
    ( v3_pre_topc(esk4_3(X1,X2,X3),X1)
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,esk4_3(X2,X3,X1))
    | r2_waybel_7(X2,X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,k2_yellow19(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_51,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_52,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_46,c_0_40])]),c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( m1_connsp_2(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),esk5_0,X1)
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_23]),c_0_24])]),c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk7_0,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0))
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_49]),c_0_23]),c_0_24])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),k2_yellow19(esk5_0,X1))
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk5_0)
    | ~ r1_waybel_0(esk5_0,X1,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0))
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_44]),c_0_25])).

cnf(c_0_56,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk6_0,X1)
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_connsp_2(X1,esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_37]),c_0_28]),c_0_29]),c_0_30]),c_0_23]),c_0_24])]),c_0_25]),c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( m1_connsp_2(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),esk5_0,esk7_0)
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),k2_yellow19(esk5_0,X1))
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk5_0,X1,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0))
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_23])])).

cnf(c_0_60,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk6_0,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0))
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_61,plain,(
    ! [X15,X16,X17] :
      ( ( ~ m1_connsp_2(X17,X15,X16)
        | r2_hidden(X16,k1_tops_1(X15,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(X16,k1_tops_1(X15,X17))
        | m1_connsp_2(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_62,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | m1_subset_1(k1_tops_1(X27,X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_63,plain,
    ( r2_waybel_7(X1,X2,X3)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),k2_yellow19(esk5_0,esk6_0))
    | m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_28]),c_0_31]),c_0_60])).

fof(c_0_65,plain,(
    ! [X33,X34] :
      ( ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | v3_pre_topc(k1_tops_1(X33,X34),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_66,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_23]),c_0_24])]),c_0_41])).

cnf(c_0_69,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_66,c_0_26])).

cnf(c_0_71,plain,
    ( r2_hidden(X4,X2)
    | ~ r2_waybel_7(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_23])])).

cnf(c_0_73,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_23]),c_0_24])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk7_0,k1_tops_1(esk5_0,X1))
    | ~ m1_connsp_2(X1,esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)),X1)
    | ~ r2_waybel_7(esk5_0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_23]),c_0_24])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0))
    | r2_waybel_7(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk7_0,k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)))
    | r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_33])).

cnf(c_0_78,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)),k2_yellow19(esk5_0,esk6_0))
    | r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

fof(c_0_80,plain,(
    ! [X46,X47,X48,X49] :
      ( ( ~ r1_waybel_0(X46,X47,X48)
        | r1_waybel_0(X46,X47,X49)
        | ~ r1_tarski(X48,X49)
        | v2_struct_0(X47)
        | ~ l1_waybel_0(X47,X46)
        | v2_struct_0(X46)
        | ~ l1_struct_0(X46) )
      & ( ~ r2_waybel_0(X46,X47,X48)
        | r2_waybel_0(X46,X47,X49)
        | ~ r1_tarski(X48,X49)
        | v2_struct_0(X47)
        | ~ l1_waybel_0(X47,X46)
        | v2_struct_0(X46)
        | ~ l1_struct_0(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).

cnf(c_0_81,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk6_0,k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)))
    | r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_28])]),c_0_31]),c_0_25])).

cnf(c_0_82,plain,
    ( r2_hidden(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,esk1_4(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k10_yellow_6(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_83,plain,
    ( r1_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ r1_tarski(X3,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk6_0,k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)))
    | r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_56]),c_0_23])])).

fof(c_0_85,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | r1_tarski(k1_tops_1(X38,X39),X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,k10_yellow_6(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_waybel_0(X2,X3,esk1_4(X2,X3,k10_yellow_6(X2,X3),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_waybel_0(X3,X2)
    | ~ v7_waybel_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_82]),c_0_18])).

cnf(c_0_87,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk6_0,X1)
    | r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0))
    | ~ r1_tarski(k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)),X1)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_28])]),c_0_31]),c_0_25])).

cnf(c_0_88,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk7_0,k10_yellow_6(esk5_0,X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk5_0,X1,esk1_4(esk5_0,X1,k10_yellow_6(esk5_0,X1),esk7_0))
    | ~ l1_waybel_0(X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_90,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk6_0,X1)
    | r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0))
    | ~ r1_tarski(k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_56]),c_0_23])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk5_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)),esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_68]),c_0_23])])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0))
    | ~ r1_waybel_0(esk5_0,esk6_0,esk1_4(esk5_0,esk6_0,k10_yellow_6(esk5_0,esk6_0),esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk7_0,k10_yellow_6(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_waybel_7(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_93])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_42]),c_0_23]),c_0_24])])).

cnf(c_0_96,negated_conjecture,
    ( m1_connsp_2(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),esk5_0,X1)
    | ~ v3_pre_topc(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),esk5_0)
    | ~ r2_hidden(X1,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_95]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_97,negated_conjecture,
    ( m1_connsp_2(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),esk5_0,X1)
    | ~ r2_hidden(X1,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_48]),c_0_23]),c_0_24])]),c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk7_0,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_49]),c_0_23]),c_0_24])])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),k2_yellow19(esk5_0,X1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk5_0)
    | ~ r1_waybel_0(esk5_0,X1,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0))
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_95]),c_0_25])).

cnf(c_0_100,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk6_0,X1)
    | ~ m1_connsp_2(X1,esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_93]),c_0_28]),c_0_29]),c_0_30]),c_0_23]),c_0_24])]),c_0_25]),c_0_31])).

cnf(c_0_101,negated_conjecture,
    ( m1_connsp_2(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),k2_yellow19(esk5_0,X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk5_0,X1,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0))
    | ~ l1_waybel_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_56]),c_0_23])])).

cnf(c_0_103,negated_conjecture,
    ( r1_waybel_0(esk5_0,esk6_0,esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk4_3(esk5_0,k2_yellow19(esk5_0,esk6_0),esk7_0),k2_yellow19(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_28]),c_0_103])]),c_0_31])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_104]),c_0_23]),c_0_24])]),c_0_94]),
    [proof]).

%------------------------------------------------------------------------------
