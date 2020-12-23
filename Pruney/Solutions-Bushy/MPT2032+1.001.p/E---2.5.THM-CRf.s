%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2032+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 201 expanded)
%              Number of clauses        :   30 (  63 expanded)
%              Number of leaves         :    5 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  219 (1660 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_waybel_9,conjecture,(
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
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r3_waybel_9(X1,X3,X4)
                   => r3_waybel_9(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).

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

fof(c_0_5,negated_conjecture,(
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
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_waybel_9(X1,X3,X4)
                     => r3_waybel_9(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_waybel_9])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r3_waybel_9(X5,X6,X7)
        | ~ m1_connsp_2(X8,X5,X7)
        | r2_waybel_0(X5,X6,X8)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | v2_struct_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_connsp_2(esk1_3(X5,X6,X7),X5,X7)
        | r3_waybel_9(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | v2_struct_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_waybel_0(X5,X6,esk1_3(X5,X6,X7))
        | r3_waybel_9(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | v2_struct_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v4_orders_2(esk3_0)
    & v7_waybel_0(esk3_0)
    & l1_waybel_0(esk3_0,esk2_0)
    & m2_yellow_6(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & r3_waybel_9(esk2_0,esk4_0,esk5_0)
    & ~ r3_waybel_9(esk2_0,esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( m1_connsp_2(esk1_3(X1,X2,X3),X1,X3)
    | r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_14,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v2_struct_0(X13)
        | ~ m2_yellow_6(X13,X11,X12)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11) )
      & ( v4_orders_2(X13)
        | ~ m2_yellow_6(X13,X11,X12)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11) )
      & ( v7_waybel_0(X13)
        | ~ m2_yellow_6(X13,X11,X12)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11) )
      & ( l1_waybel_0(X13,X11)
        | ~ m2_yellow_6(X13,X11,X12)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | v2_struct_0(X12)
        | ~ v4_orders_2(X12)
        | ~ v7_waybel_0(X12)
        | ~ l1_waybel_0(X12,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_15,plain,
    ( r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_connsp_2(X4,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( m1_connsp_2(esk1_3(esk2_0,X1,esk5_0),esk2_0,esk5_0)
    | r3_waybel_9(esk2_0,X1,esk5_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( ~ r3_waybel_9(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m2_yellow_6(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( v7_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_25,plain,(
    ! [X14,X15,X16,X17] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | v2_struct_0(X15)
      | ~ v4_orders_2(X15)
      | ~ v7_waybel_0(X15)
      | ~ l1_waybel_0(X15,X14)
      | ~ m2_yellow_6(X16,X14,X15)
      | ~ r2_waybel_0(X14,X16,X17)
      | r2_waybel_0(X14,X15,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

cnf(c_0_26,negated_conjecture,
    ( r2_waybel_0(esk2_0,X1,X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X2,esk2_0,esk5_0)
    | ~ r3_waybel_9(esk2_0,X1,esk5_0)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_9]),c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( m1_connsp_2(esk1_3(esk2_0,esk3_0,esk5_0),esk2_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_28,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( ~ l1_struct_0(esk2_0)
    | ~ v2_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_17])]),c_0_19]),c_0_12])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r2_waybel_0(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk5_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk2_0,X1,esk5_0)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r3_waybel_9(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_23]),c_0_24]),c_0_29]),c_0_17])]),c_0_19]),c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( r2_waybel_0(esk2_0,esk3_0,X1)
    | ~ r2_waybel_0(esk2_0,esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_22]),c_0_23]),c_0_24]),c_0_29]),c_0_17])]),c_0_19]),c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( r2_waybel_0(esk2_0,esk4_0,esk1_3(esk2_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_38,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_39,negated_conjecture,
    ( r2_waybel_0(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_9]),c_0_17]),c_0_10]),c_0_11])]),c_0_18]),c_0_19]),c_0_12]),
    [proof]).

%------------------------------------------------------------------------------
