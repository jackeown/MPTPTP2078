%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t26_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 353 expanded)
%              Number of clauses        :   30 ( 112 expanded)
%              Number of leaves         :    6 (  87 expanded)
%              Depth                    :    9
%              Number of atoms          :  200 (2652 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   35 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_yellow_6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/yellow_6__t26_yellow_6.p',t26_yellow_6)).

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
    file('/export/starexec/sandbox/benchmark/yellow_6__t26_yellow_6.p',d11_waybel_0)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t26_yellow_6.p',dt_l1_waybel_0)).

fof(d5_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ( v7_waybel_0(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                    & r1_orders_2(X1,X2,X4)
                    & r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t26_yellow_6.p',d5_yellow_6)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t26_yellow_6.p',symmetry_r1_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t26_yellow_6.p',t3_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t26_yellow_6])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X16,X17,X18] :
      ( ( m1_subset_1(esk5_3(X12,X13,X14),u1_struct_0(X13))
        | ~ r1_waybel_0(X12,X13,X14)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r1_orders_2(X13,esk5_3(X12,X13,X14),X16)
        | r2_hidden(k2_waybel_0(X12,X13,X16),X14)
        | ~ r1_waybel_0(X12,X13,X14)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( m1_subset_1(esk6_4(X12,X13,X17,X18),u1_struct_0(X13))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | r1_waybel_0(X12,X13,X17)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( r1_orders_2(X13,X18,esk6_4(X12,X13,X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | r1_waybel_0(X12,X13,X17)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( ~ r2_hidden(k2_waybel_0(X12,X13,esk6_4(X12,X13,X17,X18)),X17)
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | r1_waybel_0(X12,X13,X17)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & v7_waybel_0(esk2_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & r1_waybel_0(esk1_0,esk2_0,esk3_0)
    & r1_waybel_0(esk1_0,esk2_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X35,X36] :
      ( ~ l1_struct_0(X35)
      | ~ l1_waybel_0(X36,X35)
      | l1_orders_2(X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X26] :
      ( ( m1_subset_1(esk7_3(X20,X21,X22),u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ v7_waybel_0(X20)
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20) )
      & ( r1_orders_2(X20,X21,esk7_3(X20,X21,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ v7_waybel_0(X20)
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20) )
      & ( r1_orders_2(X20,X22,esk7_3(X20,X21,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ v7_waybel_0(X20)
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20) )
      & ( m1_subset_1(esk8_1(X20),u1_struct_0(X20))
        | v7_waybel_0(X20)
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20) )
      & ( m1_subset_1(esk9_1(X20),u1_struct_0(X20))
        | v7_waybel_0(X20)
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X20))
        | ~ r1_orders_2(X20,esk8_1(X20),X26)
        | ~ r1_orders_2(X20,esk9_1(X20),X26)
        | v7_waybel_0(X20)
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_yellow_6])])])])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_19,plain,(
    ! [X49,X50] :
      ( ~ r1_xboole_0(X49,X50)
      | r1_xboole_0(X50,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,esk7_3(X1,X3,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14])])).

cnf(c_0_23,negated_conjecture,
    ( v7_waybel_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_18]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

fof(c_0_26,plain,(
    ! [X57,X58,X60,X61,X62] :
      ( ( r2_hidden(esk14_2(X57,X58),X57)
        | r1_xboole_0(X57,X58) )
      & ( r2_hidden(esk14_2(X57,X58),X58)
        | r1_xboole_0(X57,X58) )
      & ( ~ r2_hidden(X62,X60)
        | ~ r2_hidden(X62,X61)
        | ~ r1_xboole_0(X60,X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk7_3(esk2_0,esk5_3(esk1_0,esk2_0,esk4_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_3(esk2_0,X1,esk5_3(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_22]),c_0_23])]),c_0_15])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X2,esk7_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(k2_waybel_0(X3,X2,X1),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk5_3(X3,X2,X4),X1)
    | ~ r1_waybel_0(X3,X2,X4)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_3(esk1_0,esk2_0,esk3_0),esk7_3(esk2_0,esk5_3(esk1_0,esk2_0,esk4_0),esk5_3(esk1_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_3(esk2_0,esk5_3(esk1_0,esk2_0,esk4_0),esk5_3(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk7_3(esk2_0,X1,esk5_3(esk1_0,esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_22]),c_0_23])]),c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_3(esk2_0,esk5_3(esk1_0,esk2_0,esk4_0),esk5_3(esk1_0,esk2_0,esk3_0))),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_18]),c_0_13]),c_0_14])]),c_0_16]),c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_3(esk1_0,esk2_0,esk4_0),esk7_3(esk2_0,esk5_3(esk1_0,esk2_0,esk4_0),esk5_3(esk1_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(k2_waybel_0(esk1_0,esk2_0,esk7_3(esk2_0,esk5_3(esk1_0,esk2_0,esk4_0),esk5_3(esk1_0,esk2_0,esk3_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_40]),c_0_36]),c_0_12]),c_0_13]),c_0_14])]),c_0_41]),c_0_16]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
