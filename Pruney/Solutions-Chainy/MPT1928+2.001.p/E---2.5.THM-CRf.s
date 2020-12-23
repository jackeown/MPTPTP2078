%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 715 expanded)
%              Number of clauses        :   37 ( 234 expanded)
%              Number of leaves         :    5 ( 174 expanded)
%              Depth                    :   13
%              Number of atoms          :  211 (5337 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X20,X21] :
      ( ~ l1_struct_0(X20)
      | ~ l1_waybel_0(X21,X20)
      | l1_orders_2(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & l1_struct_0(esk7_0)
    & ~ v2_struct_0(esk8_0)
    & v4_orders_2(esk8_0)
    & v7_waybel_0(esk8_0)
    & l1_waybel_0(esk8_0,esk7_0)
    & r1_waybel_0(esk7_0,esk8_0,esk9_0)
    & r1_waybel_0(esk7_0,esk8_0,esk10_0)
    & r1_xboole_0(esk9_0,esk10_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X22,X23,X24,X28] :
      ( ( m1_subset_1(esk4_3(X22,X23,X24),u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,X23,esk4_3(X22,X23,X24))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,X24,esk4_3(X22,X23,X24))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk5_1(X22),u1_struct_0(X22))
        | v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk6_1(X22),u1_struct_0(X22))
        | v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X22))
        | ~ r1_orders_2(X22,esk5_1(X22),X28)
        | ~ r1_orders_2(X22,esk6_1(X22),X28)
        | v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_yellow_6])])])])])])).

cnf(c_0_9,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X12,X13,X14,X16,X17,X18] :
      ( ( m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X13))
        | ~ r1_waybel_0(X12,X13,X14)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r1_orders_2(X13,esk2_3(X12,X13,X14),X16)
        | r2_hidden(k2_waybel_0(X12,X13,X16),X14)
        | ~ r1_waybel_0(X12,X13,X14)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( m1_subset_1(esk3_4(X12,X13,X17,X18),u1_struct_0(X13))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | r1_waybel_0(X12,X13,X17)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( r1_orders_2(X13,X18,esk3_4(X12,X13,X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | r1_waybel_0(X12,X13,X17)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( ~ r2_hidden(k2_waybel_0(X12,X13,esk3_4(X12,X13,X17,X18)),X17)
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | r1_waybel_0(X12,X13,X17)
        | v2_struct_0(X13)
        | ~ l1_waybel_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X2,esk4_3(X1,X3,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v7_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( r1_waybel_0(esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk4_3(esk8_0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_3(esk7_0,esk8_0,esk10_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_10]),c_0_11])]),c_0_16]),c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_3(esk8_0,X1,X2),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_21]),c_0_10]),c_0_11])]),c_0_16]),c_0_19])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X2,esk4_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_3(esk8_0,X1,esk2_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk4_3(esk8_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_30,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(k2_waybel_0(X3,X2,X1),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk2_3(X3,X2,X4),X1)
    | ~ r1_waybel_0(X3,X2,X4)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk8_0,esk2_3(esk7_0,esk8_0,esk9_0),esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk4_3(esk8_0,X1,esk2_3(esk7_0,esk8_0,esk9_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk7_0,esk8_0,esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0))),esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_21]),c_0_10]),c_0_11])]),c_0_19]),c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(k2_waybel_0(esk7_0,esk8_0,esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0))),X1)
    | ~ r1_xboole_0(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk7_0,esk8_0,esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0))),esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_37]),c_0_33]),c_0_18]),c_0_10]),c_0_11])]),c_0_19]),c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_xboole_0(esk10_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_2(esk10_0,esk9_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk10_0,esk9_0),X1)
    | ~ r1_xboole_0(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(esk10_0,esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S047A
% 0.20/0.40  # and selection function PSelectComplexPreferNEQ.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.043 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t26_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:~(((r1_waybel_0(X1,X2,X3)&r1_waybel_0(X1,X2,X4))&r1_xboole_0(X3,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_6)).
% 0.20/0.40  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.20/0.40  fof(d5_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>(v7_waybel_0(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>?[X4]:((m1_subset_1(X4,u1_struct_0(X1))&r1_orders_2(X1,X2,X4))&r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_yellow_6)).
% 0.20/0.40  fof(d11_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r2_hidden(k2_waybel_0(X1,X2,X5),X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 0.20/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.40  fof(c_0_5, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:~(((r1_waybel_0(X1,X2,X3)&r1_waybel_0(X1,X2,X4))&r1_xboole_0(X3,X4)))))), inference(assume_negation,[status(cth)],[t26_yellow_6])).
% 0.20/0.40  fof(c_0_6, plain, ![X20, X21]:(~l1_struct_0(X20)|(~l1_waybel_0(X21,X20)|l1_orders_2(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.20/0.40  fof(c_0_7, negated_conjecture, ((~v2_struct_0(esk7_0)&l1_struct_0(esk7_0))&((((~v2_struct_0(esk8_0)&v4_orders_2(esk8_0))&v7_waybel_0(esk8_0))&l1_waybel_0(esk8_0,esk7_0))&((r1_waybel_0(esk7_0,esk8_0,esk9_0)&r1_waybel_0(esk7_0,esk8_0,esk10_0))&r1_xboole_0(esk9_0,esk10_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.20/0.40  fof(c_0_8, plain, ![X22, X23, X24, X28]:((((m1_subset_1(esk4_3(X22,X23,X24),u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|~v7_waybel_0(X22)|(v2_struct_0(X22)|~l1_orders_2(X22)))&(r1_orders_2(X22,X23,esk4_3(X22,X23,X24))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|~v7_waybel_0(X22)|(v2_struct_0(X22)|~l1_orders_2(X22))))&(r1_orders_2(X22,X24,esk4_3(X22,X23,X24))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|~v7_waybel_0(X22)|(v2_struct_0(X22)|~l1_orders_2(X22))))&((m1_subset_1(esk5_1(X22),u1_struct_0(X22))|v7_waybel_0(X22)|(v2_struct_0(X22)|~l1_orders_2(X22)))&((m1_subset_1(esk6_1(X22),u1_struct_0(X22))|v7_waybel_0(X22)|(v2_struct_0(X22)|~l1_orders_2(X22)))&(~m1_subset_1(X28,u1_struct_0(X22))|~r1_orders_2(X22,esk5_1(X22),X28)|~r1_orders_2(X22,esk6_1(X22),X28)|v7_waybel_0(X22)|(v2_struct_0(X22)|~l1_orders_2(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_yellow_6])])])])])])).
% 0.20/0.40  cnf(c_0_9, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.40  cnf(c_0_10, negated_conjecture, (l1_waybel_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_11, negated_conjecture, (l1_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  fof(c_0_12, plain, ![X12, X13, X14, X16, X17, X18]:(((m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X13))|~r1_waybel_0(X12,X13,X14)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))&(~m1_subset_1(X16,u1_struct_0(X13))|(~r1_orders_2(X13,esk2_3(X12,X13,X14),X16)|r2_hidden(k2_waybel_0(X12,X13,X16),X14))|~r1_waybel_0(X12,X13,X14)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12))))&((m1_subset_1(esk3_4(X12,X13,X17,X18),u1_struct_0(X13))|~m1_subset_1(X18,u1_struct_0(X13))|r1_waybel_0(X12,X13,X17)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))&((r1_orders_2(X13,X18,esk3_4(X12,X13,X17,X18))|~m1_subset_1(X18,u1_struct_0(X13))|r1_waybel_0(X12,X13,X17)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))&(~r2_hidden(k2_waybel_0(X12,X13,esk3_4(X12,X13,X17,X18)),X17)|~m1_subset_1(X18,u1_struct_0(X13))|r1_waybel_0(X12,X13,X17)|(v2_struct_0(X13)|~l1_waybel_0(X13,X12))|(v2_struct_0(X12)|~l1_struct_0(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).
% 0.20/0.40  cnf(c_0_13, plain, (r1_orders_2(X1,X2,esk4_3(X1,X3,X2))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v7_waybel_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_14, negated_conjecture, (v7_waybel_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_17, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_20, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v7_waybel_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (r1_waybel_0(esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (r1_orders_2(esk8_0,X1,esk4_3(esk8_0,X2,X1))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk2_3(esk7_0,esk8_0,esk10_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_10]), c_0_11])]), c_0_16]), c_0_19])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_3(esk8_0,X1,X2),u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk2_3(esk7_0,esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_21]), c_0_10]), c_0_11])]), c_0_16]), c_0_19])).
% 0.20/0.40  cnf(c_0_26, plain, (r1_orders_2(X1,X2,esk4_3(X1,X2,X3))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v7_waybel_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (r1_orders_2(esk8_0,X1,esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),X1))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_3(esk8_0,X1,esk2_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (r1_orders_2(esk8_0,X1,esk4_3(esk8_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.40  fof(c_0_30, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.40  cnf(c_0_31, plain, (r2_hidden(k2_waybel_0(X3,X2,X1),X4)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,esk2_3(X3,X2,X4),X1)|~r1_waybel_0(X3,X2,X4)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (r1_orders_2(esk8_0,esk2_3(esk7_0,esk8_0,esk9_0),esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_28, c_0_23])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (r1_orders_2(esk8_0,X1,esk4_3(esk8_0,X1,esk2_3(esk7_0,esk8_0,esk9_0)))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.20/0.40  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (r2_hidden(k2_waybel_0(esk7_0,esk8_0,esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0))),esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_21]), c_0_10]), c_0_11])]), c_0_19]), c_0_16])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (r1_orders_2(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (~r2_hidden(k2_waybel_0(esk7_0,esk8_0,esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0))),X1)|~r1_xboole_0(X1,esk9_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (r2_hidden(k2_waybel_0(esk7_0,esk8_0,esk4_3(esk8_0,esk2_3(esk7_0,esk8_0,esk10_0),esk2_3(esk7_0,esk8_0,esk9_0))),esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_37]), c_0_33]), c_0_18]), c_0_10]), c_0_11])]), c_0_19]), c_0_16])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (~r1_xboole_0(esk10_0,esk9_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_2(esk10_0,esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.40  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk1_2(esk10_0,esk9_0),X1)|~r1_xboole_0(X1,esk10_0)), inference(spm,[status(thm)],[c_0_35, c_0_42])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(esk10_0,esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_43])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (r1_xboole_0(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 48
% 0.20/0.40  # Proof object clause steps            : 37
% 0.20/0.40  # Proof object formula steps           : 11
% 0.20/0.40  # Proof object conjectures             : 31
% 0.20/0.40  # Proof object clause conjectures      : 28
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 17
% 0.20/0.40  # Proof object initial formulas used   : 5
% 0.20/0.40  # Proof object generating inferences   : 20
% 0.20/0.40  # Proof object simplifying inferences  : 37
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 5
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 24
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 24
% 0.20/0.40  # Processed clauses                    : 102
% 0.20/0.40  # ...of these trivial                  : 2
% 0.20/0.40  # ...subsumed                          : 6
% 0.20/0.40  # ...remaining for further processing  : 94
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 119
% 0.20/0.40  # ...of the previous two non-trivial   : 114
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 119
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 0
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 70
% 0.20/0.40  #    Positive orientable unit clauses  : 28
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 5
% 0.20/0.40  #    Non-unit-clauses                  : 37
% 0.20/0.40  # Current number of unprocessed clauses: 59
% 0.20/0.40  # ...number of literals in the above   : 135
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 24
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 224
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 51
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.40  # Unit Clause-clause subsumption calls : 54
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 23
% 0.20/0.40  # BW rewrite match successes           : 0
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 5342
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.046 s
% 0.20/0.40  # System time              : 0.011 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
