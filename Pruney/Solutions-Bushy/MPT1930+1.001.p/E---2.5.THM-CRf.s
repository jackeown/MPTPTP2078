%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1930+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 348 expanded)
%              Number of clauses        :   30 ( 114 expanded)
%              Number of leaves         :    5 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :  239 (2420 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
             => r2_waybel_0(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_6)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( r1_waybel_0(X1,X2,X3)
               => r2_waybel_0(X1,X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_yellow_6])).

fof(c_0_6,plain,(
    ! [X29,X30] :
      ( ~ l1_struct_0(X29)
      | ~ l1_waybel_0(X30,X29)
      | l1_orders_2(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & l1_struct_0(esk8_0)
    & ~ v2_struct_0(esk9_0)
    & v4_orders_2(esk9_0)
    & v7_waybel_0(esk9_0)
    & l1_waybel_0(esk9_0,esk8_0)
    & r1_waybel_0(esk8_0,esk9_0,esk10_0)
    & ~ r2_waybel_0(esk8_0,esk9_0,esk10_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X14,X15,X16,X17,X19,X21] :
      ( ( m1_subset_1(esk3_4(X14,X15,X16,X17),u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ r2_waybel_0(X14,X15,X16)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) )
      & ( r1_orders_2(X15,X17,esk3_4(X14,X15,X16,X17))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ r2_waybel_0(X14,X15,X16)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) )
      & ( r2_hidden(k2_waybel_0(X14,X15,esk3_4(X14,X15,X16,X17)),X16)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ r2_waybel_0(X14,X15,X16)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) )
      & ( m1_subset_1(esk4_3(X14,X15,X19),u1_struct_0(X15))
        | r2_waybel_0(X14,X15,X19)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X15))
        | ~ r1_orders_2(X15,esk4_3(X14,X15,X19),X21)
        | ~ r2_hidden(k2_waybel_0(X14,X15,X21),X19)
        | r2_waybel_0(X14,X15,X19)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

fof(c_0_9,plain,(
    ! [X22,X23,X24,X28] :
      ( ( m1_subset_1(esk5_3(X22,X23,X24),u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,X23,esk5_3(X22,X23,X24))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,X24,esk5_3(X22,X23,X24))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk6_1(X22),u1_struct_0(X22))
        | v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk7_1(X22),u1_struct_0(X22))
        | v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X22))
        | ~ r1_orders_2(X22,esk6_1(X22),X28)
        | ~ r1_orders_2(X22,esk7_1(X22),X28)
        | v7_waybel_0(X22)
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_yellow_6])])])])])])).

cnf(c_0_10,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_16,plain,(
    ! [X6,X7,X8,X10,X11,X12] :
      ( ( m1_subset_1(esk1_3(X6,X7,X8),u1_struct_0(X7))
        | ~ r1_waybel_0(X6,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,esk1_3(X6,X7,X8),X10)
        | r2_hidden(k2_waybel_0(X6,X7,X10),X8)
        | ~ r1_waybel_0(X6,X7,X8)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( m1_subset_1(esk2_4(X6,X7,X11,X12),u1_struct_0(X7))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,X11)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( r1_orders_2(X7,X12,esk2_4(X6,X7,X11,X12))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,X11)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) )
      & ( ~ r2_hidden(k2_waybel_0(X6,X7,esk2_4(X6,X7,X11,X12)),X11)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_waybel_0(X6,X7,X11)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_17,plain,
    ( r1_orders_2(X1,X2,esk5_3(X1,X3,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( v7_waybel_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_waybel_0(esk8_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( r2_waybel_0(esk8_0,esk9_0,X1)
    | m1_subset_1(esk4_3(esk8_0,esk9_0,X1),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_12])]),c_0_14]),c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_waybel_0(esk8_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,esk5_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk5_3(esk9_0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_3(esk8_0,esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_3(esk9_0,X1,X2),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_19])]),c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_11]),c_0_12])]),c_0_14]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk5_3(esk9_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19])]),c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk5_3(esk9_0,esk4_3(esk8_0,esk9_0,esk10_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_3(esk9_0,X1,esk1_3(esk8_0,esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk5_3(esk9_0,X1,esk1_3(esk8_0,esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(k2_waybel_0(X3,X2,X1),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk1_3(X3,X2,X4),X1)
    | ~ r1_waybel_0(X3,X2,X4)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk9_0,esk1_3(esk8_0,esk9_0,esk10_0),esk5_3(esk9_0,esk4_3(esk8_0,esk9_0,esk10_0),esk1_3(esk8_0,esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_3(esk9_0,esk4_3(esk8_0,esk9_0,esk10_0),esk1_3(esk8_0,esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_37,plain,
    ( r2_waybel_0(X3,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,esk4_3(X3,X2,X4),X1)
    | ~ r2_hidden(k2_waybel_0(X3,X2,X1),X4)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk9_0,esk4_3(esk8_0,esk9_0,esk10_0),esk5_3(esk9_0,esk4_3(esk8_0,esk9_0,esk10_0),esk1_3(esk8_0,esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk8_0,esk9_0,esk5_3(esk9_0,esk4_3(esk8_0,esk9_0,esk10_0),esk1_3(esk8_0,esk9_0,esk10_0))),esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_24]),c_0_11]),c_0_12])]),c_0_15]),c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_36]),c_0_11]),c_0_12])]),c_0_20]),c_0_15]),c_0_14]),c_0_39])]),
    [proof]).

%------------------------------------------------------------------------------
