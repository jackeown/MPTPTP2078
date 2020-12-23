%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_9__t31_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:09 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 203 expanded)
%              Number of clauses        :   32 (  65 expanded)
%              Number of leaves         :    5 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  223 (1664 expanded)
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
    file('/export/starexec/sandbox/benchmark/waybel_9__t31_waybel_9.p',t31_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/waybel_9__t31_waybel_9.p',dt_m2_yellow_6)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t31_waybel_9.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/waybel_9__t31_waybel_9.p',d9_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/waybel_9__t31_waybel_9.p',t27_yellow_6)).

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
    ! [X23,X24,X25] :
      ( ( ~ v2_struct_0(X25)
        | ~ m2_yellow_6(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23) )
      & ( v4_orders_2(X25)
        | ~ m2_yellow_6(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23) )
      & ( v7_waybel_0(X25)
        | ~ m2_yellow_6(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23) )
      & ( l1_waybel_0(X25,X23)
        | ~ m2_yellow_6(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v2_struct_0(X24)
        | ~ v4_orders_2(X24)
        | ~ v7_waybel_0(X24)
        | ~ l1_waybel_0(X24,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & v7_waybel_0(esk2_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & m2_yellow_6(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & r3_waybel_9(esk1_0,esk3_0,esk4_0)
    & ~ r3_waybel_9(esk1_0,esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ r3_waybel_9(X11,X12,X13)
        | ~ m1_connsp_2(X14,X11,X13)
        | r2_waybel_0(X11,X12,X14)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | v2_struct_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_connsp_2(esk5_3(X11,X12,X13),X11,X13)
        | r3_waybel_9(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | v2_struct_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r2_waybel_0(X11,X12,esk5_3(X11,X12,X13))
        | r3_waybel_9(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | v2_struct_0(X12)
        | ~ l1_waybel_0(X12,X11)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_waybel_9])])])])])])).

cnf(c_0_10,plain,
    ( l1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m2_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_connsp_2(X4,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ v2_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_26,plain,
    ( m1_connsp_2(esk5_3(X1,X2,X3),X1,X3)
    | r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_27,plain,(
    ! [X41,X42,X43,X44] :
      ( v2_struct_0(X41)
      | ~ l1_struct_0(X41)
      | v2_struct_0(X42)
      | ~ v4_orders_2(X42)
      | ~ v7_waybel_0(X42)
      | ~ l1_waybel_0(X42,X41)
      | ~ m2_yellow_6(X43,X41,X42)
      | ~ r2_waybel_0(X41,X43,X44)
      | r2_waybel_0(X41,X42,X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_yellow_6])])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_waybel_0(esk1_0,X1,X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X2,esk1_0,esk4_0)
    | ~ r3_waybel_9(esk1_0,X1,esk4_0)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_18]),c_0_22])]),c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( r3_waybel_9(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( m1_connsp_2(esk5_3(esk1_0,X1,esk4_0),esk1_0,esk4_0)
    | r3_waybel_9(esk1_0,X1,esk4_0)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_18]),c_0_22])]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,esk5_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_waybel_0(X1,X2,X4)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m2_yellow_6(X3,X1,X2)
    | ~ r2_waybel_0(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk3_0,X1)
    | ~ m1_connsp_2(X1,esk1_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_connsp_2(esk5_3(esk1_0,esk2_0,esk4_0),esk1_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_12]),c_0_33]),c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( r3_waybel_9(esk1_0,X1,esk4_0)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(esk1_0,X1,esk5_3(esk1_0,X1,esk4_0))
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_21]),c_0_18]),c_0_22])]),c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk2_0,X1)
    | ~ r2_waybel_0(esk1_0,esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16]),c_0_24])])).

cnf(c_0_40,negated_conjecture,
    ( r2_waybel_0(esk1_0,esk3_0,esk5_3(esk1_0,esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_waybel_0(esk1_0,esk2_0,esk5_3(esk1_0,esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_12]),c_0_33]),c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
