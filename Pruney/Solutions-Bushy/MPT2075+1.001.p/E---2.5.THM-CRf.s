%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2075+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:12 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 585 expanded)
%              Number of clauses        :   29 ( 182 expanded)
%              Number of leaves         :    3 ( 145 expanded)
%              Depth                    :   10
%              Number of atoms          :  217 (6973 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_yellow19,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).

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

fof(c_0_3,negated_conjecture,(
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
                  ( m1_subset_1(X3,u1_struct_0(X1))
                  & r3_waybel_9(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_yellow19])).

fof(c_0_4,plain,(
    ! [X7,X9] :
      ( ( ~ v2_struct_0(esk2_1(X7))
        | v1_compts_1(X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( v4_orders_2(esk2_1(X7))
        | v1_compts_1(X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( v7_waybel_0(esk2_1(X7))
        | v1_compts_1(X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( l1_waybel_0(esk2_1(X7),X7)
        | v1_compts_1(X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk2_1(X7),k6_yellow_6(X7))
        | v1_compts_1(X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ r3_waybel_9(X7,esk2_1(X7),X9)
        | v1_compts_1(X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_yellow19])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X12,X13] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ( ~ v2_struct_0(esk4_0)
        | ~ v1_compts_1(esk3_0) )
      & ( v4_orders_2(esk4_0)
        | ~ v1_compts_1(esk3_0) )
      & ( v7_waybel_0(esk4_0)
        | ~ v1_compts_1(esk3_0) )
      & ( l1_waybel_0(esk4_0,esk3_0)
        | ~ v1_compts_1(esk3_0) )
      & ( ~ m1_subset_1(X12,u1_struct_0(esk3_0))
        | ~ r3_waybel_9(esk3_0,esk4_0,X12)
        | ~ v1_compts_1(esk3_0) )
      & ( m1_subset_1(esk5_1(X13),u1_struct_0(esk3_0))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,esk3_0)
        | v1_compts_1(esk3_0) )
      & ( r3_waybel_9(esk3_0,X13,esk5_1(X13))
        | v2_struct_0(X13)
        | ~ v4_orders_2(X13)
        | ~ v7_waybel_0(X13)
        | ~ l1_waybel_0(X13,esk3_0)
        | v1_compts_1(esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

cnf(c_0_6,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk2_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r3_waybel_9(esk3_0,X1,esk5_1(X1))
    | v2_struct_0(X1)
    | v1_compts_1(esk3_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk5_1(X1),u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | v1_compts_1(esk3_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v1_compts_1(esk3_0)
    | v2_struct_0(esk2_1(esk3_0))
    | ~ l1_waybel_0(esk2_1(esk3_0),esk3_0)
    | ~ v7_waybel_0(esk2_1(esk3_0))
    | ~ v4_orders_2(esk2_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9])]),c_0_10]),c_0_11])).

cnf(c_0_13,plain,
    ( l1_waybel_0(esk2_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( v1_compts_1(esk3_0)
    | v2_struct_0(esk2_1(esk3_0))
    | ~ v7_waybel_0(esk2_1(esk3_0))
    | ~ v4_orders_2(esk2_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_15,plain,
    ( v7_waybel_0(esk2_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_16,plain,(
    ! [X4,X5] :
      ( ( m1_subset_1(esk1_2(X4,X5),u1_struct_0(X4))
        | v2_struct_0(X5)
        | ~ v4_orders_2(X5)
        | ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,X4)
        | ~ v1_compts_1(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r3_waybel_9(X4,X5,esk1_2(X4,X5))
        | v2_struct_0(X5)
        | ~ v4_orders_2(X5)
        | ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,X4)
        | ~ v1_compts_1(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( v1_compts_1(esk3_0)
    | v2_struct_0(esk2_1(esk3_0))
    | ~ v4_orders_2(esk2_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_18,plain,
    ( v4_orders_2(esk2_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r3_waybel_9(esk3_0,esk4_0,X1)
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk2_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( v1_compts_1(esk3_0)
    | v2_struct_0(esk2_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r3_waybel_9(esk3_0,esk4_0,esk1_2(esk3_0,X1))
    | ~ l1_waybel_0(X1,esk3_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v1_compts_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( v1_compts_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk3_0)
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,negated_conjecture,
    ( v7_waybel_0(esk4_0)
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( v4_orders_2(esk4_0)
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_29,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ r3_waybel_9(esk3_0,esk4_0,esk1_2(esk3_0,X1))
    | ~ l1_waybel_0(X1,esk3_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_30,plain,
    ( r3_waybel_9(X1,X2,esk1_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( v7_waybel_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_24])])).

cnf(c_0_33,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_24])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24])])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_24]),c_0_8]),c_0_9])]),c_0_34]),c_0_10]),
    [proof]).

%------------------------------------------------------------------------------
