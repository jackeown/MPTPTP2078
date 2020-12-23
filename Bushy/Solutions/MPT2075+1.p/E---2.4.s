%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t35_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:52 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   40 (1574 expanded)
%              Number of clauses        :   33 ( 491 expanded)
%              Number of leaves         :    3 ( 391 expanded)
%              Depth                    :   14
%              Number of atoms          :  220 (18776 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t35_yellow19.p',t35_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t35_yellow19.p',l38_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/yellow19__t35_yellow19.p',l37_yellow19)).

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
      & ( ~ m1_subset_1(X6,u1_struct_0(esk1_0))
        | ~ r3_waybel_9(esk1_0,esk2_0,X6)
        | ~ v1_compts_1(esk1_0) )
      & ( m1_subset_1(esk3_1(X7),u1_struct_0(esk1_0))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,esk1_0)
        | v1_compts_1(esk1_0) )
      & ( r3_waybel_9(esk1_0,X7,esk3_1(X7))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,esk1_0)
        | v1_compts_1(esk1_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

fof(c_0_5,plain,(
    ! [X25,X27] :
      ( ( ~ v2_struct_0(esk10_1(X25))
        | v1_compts_1(X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v4_orders_2(esk10_1(X25))
        | v1_compts_1(X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v7_waybel_0(esk10_1(X25))
        | v1_compts_1(X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( l1_waybel_0(esk10_1(X25),X25)
        | v1_compts_1(X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( r2_hidden(esk10_1(X25),k6_yellow_6(X25))
        | v1_compts_1(X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ r3_waybel_9(X25,esk10_1(X25),X27)
        | v1_compts_1(X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_yellow19])])])])])])).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(esk1_0))
    | v2_struct_0(X1)
    | v1_compts_1(esk1_0)
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
    | ~ v4_orders_2(esk10_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_14,plain,
    ( v4_orders_2(esk10_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( v1_compts_1(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_waybel_9(X2,esk10_1(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_1(esk10_1(esk1_0)),u1_struct_0(esk1_0))
    | v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r3_waybel_9(esk1_0,X1,esk3_1(X1))
    | v2_struct_0(X1)
    | v1_compts_1(esk1_0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ r3_waybel_9(esk1_0,esk10_1(esk1_0),esk3_1(esk10_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ v7_waybel_0(esk10_1(esk1_0))
    | ~ v4_orders_2(esk10_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_7]),c_0_8]),c_0_9])]),c_0_10]),c_0_18])).

cnf(c_0_20,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0))
    | ~ v4_orders_2(esk10_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_12]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_21,plain,
    ( v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk10_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_struct_0(esk10_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_8]),c_0_9])]),c_0_10])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ( m1_subset_1(esk9_2(X22,X23),u1_struct_0(X22))
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ v1_compts_1(X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( r3_waybel_9(X22,X23,esk9_2(X22,X23))
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ v1_compts_1(X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l37_yellow19])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_25,negated_conjecture,
    ( v1_compts_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( v7_waybel_0(esk2_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_27,negated_conjecture,
    ( v4_orders_2(esk2_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_29,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_30,plain,
    ( r3_waybel_9(X1,X2,esk9_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_32,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_25])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_25])])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk9_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_25])])).

cnf(c_0_37,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk2_0,esk9_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_25]),c_0_8]),c_0_9])]),c_0_34]),c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk9_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_32]),c_0_33]),c_0_25]),c_0_8]),c_0_9])]),c_0_34]),c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
