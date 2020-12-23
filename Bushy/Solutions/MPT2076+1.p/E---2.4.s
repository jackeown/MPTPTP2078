%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t36_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:52 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (1926 expanded)
%              Number of clauses        :   36 ( 601 expanded)
%              Number of leaves         :    3 ( 479 expanded)
%              Depth                    :   16
%              Number of atoms          :  244 (25257 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_yellow19,conjecture,(
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
           => ~ ( r2_hidden(X2,k6_yellow_6(X1))
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r3_waybel_9(X1,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',t36_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',l38_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',l37_yellow19)).

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
             => ~ ( r2_hidden(X2,k6_yellow_6(X1))
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ~ r3_waybel_9(X1,X2,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_yellow19])).

fof(c_0_4,negated_conjecture,(
    ! [X6,X7] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ( ~ v2_struct_0(esk2_0)
        | ~ v1_compts_1(esk1_0) )
      & ( v4_orders_2(esk2_0)
        | ~ v1_compts_1(esk1_0) )
      & ( v7_waybel_0(esk2_0)
        | ~ v1_compts_1(esk1_0) )
      & ( l1_waybel_0(esk2_0,esk1_0)
        | ~ v1_compts_1(esk1_0) )
      & ( r2_hidden(esk2_0,k6_yellow_6(esk1_0))
        | ~ v1_compts_1(esk1_0) )
      & ( ~ m1_subset_1(X6,u1_struct_0(esk1_0))
        | ~ r3_waybel_9(esk1_0,esk2_0,X6)
        | ~ v1_compts_1(esk1_0) )
      & ( m1_subset_1(esk3_1(X7),u1_struct_0(esk1_0))
        | ~ r2_hidden(X7,k6_yellow_6(esk1_0))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,esk1_0)
        | v1_compts_1(esk1_0) )
      & ( r3_waybel_9(esk1_0,X7,esk3_1(X7))
        | ~ r2_hidden(X7,k6_yellow_6(esk1_0))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,esk1_0)
        | v1_compts_1(esk1_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

fof(c_0_5,plain,(
    ! [X34,X36] :
      ( ( ~ v2_struct_0(esk10_1(X34))
        | v1_compts_1(X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( v4_orders_2(esk10_1(X34))
        | v1_compts_1(X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( v7_waybel_0(esk10_1(X34))
        | v1_compts_1(X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( l1_waybel_0(esk10_1(X34),X34)
        | v1_compts_1(X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(esk10_1(X34),k6_yellow_6(X34))
        | v1_compts_1(X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ r3_waybel_9(X34,esk10_1(X34),X36)
        | v1_compts_1(X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_yellow19])])])])])])).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(esk1_0))
    | v2_struct_0(X1)
    | v1_compts_1(esk1_0)
    | ~ r2_hidden(X1,k6_yellow_6(esk1_0))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( l1_waybel_0(esk10_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_1(esk10_1(esk1_0)),u1_struct_0(esk1_0))
    | v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ r2_hidden(esk10_1(esk1_0),k6_yellow_6(esk1_0))
    | ~ v7_waybel_0(esk10_1(esk1_0))
    | ~ v4_orders_2(esk10_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_12,plain,
    ( v7_waybel_0(esk10_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_1(esk10_1(esk1_0)),u1_struct_0(esk1_0))
    | v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ r2_hidden(esk10_1(esk1_0),k6_yellow_6(esk1_0))
    | ~ v4_orders_2(esk10_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_14,plain,
    ( v4_orders_2(esk10_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_1(esk10_1(esk1_0)),u1_struct_0(esk1_0))
    | v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ r2_hidden(esk10_1(esk1_0),k6_yellow_6(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk10_1(X1),k6_yellow_6(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk10_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_1(esk10_1(esk1_0)),u1_struct_0(esk1_0))
    | v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( r3_waybel_9(esk1_0,X1,esk3_1(X1))
    | v2_struct_0(X1)
    | v1_compts_1(esk1_0)
    | ~ r2_hidden(X1,k6_yellow_6(esk1_0))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ r3_waybel_9(esk1_0,esk10_1(esk1_0),esk3_1(esk10_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ r2_hidden(esk10_1(esk1_0),k6_yellow_6(esk1_0))
    | ~ v7_waybel_0(esk10_1(esk1_0))
    | ~ v4_orders_2(esk10_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_7]),c_0_8]),c_0_9])]),c_0_10]),c_0_20])).

cnf(c_0_22,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ r2_hidden(esk10_1(esk1_0),k6_yellow_6(esk1_0))
    | ~ v4_orders_2(esk10_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_12]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ r2_hidden(esk10_1(esk1_0),k6_yellow_6(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_14]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_24,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk10_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_8]),c_0_9])]),c_0_10])).

fof(c_0_26,plain,(
    ! [X31,X32] :
      ( ( m1_subset_1(esk9_2(X31,X32),u1_struct_0(X31))
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | ~ v1_compts_1(X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r3_waybel_9(X31,X32,esk9_2(X31,X32))
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | ~ v1_compts_1(X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,negated_conjecture,
    ( v1_compts_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( v7_waybel_0(esk2_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_30,negated_conjecture,
    ( v4_orders_2(esk2_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_33,plain,
    ( r3_waybel_9(X1,X2,esk9_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_28])])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk9_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk2_0,esk9_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_28]),c_0_8]),c_0_9])]),c_0_37]),c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk9_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_35]),c_0_36]),c_0_28]),c_0_8]),c_0_9])]),c_0_37]),c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
