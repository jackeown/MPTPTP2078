%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:38 EST 2020

% Result     : CounterSatisfiable 0.15s
% Output     : Saturation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  129 (2111 expanded)
%              Number of clauses        :  116 ( 851 expanded)
%              Number of leaves         :    6 ( 489 expanded)
%              Depth                    :    9
%              Number of atoms          :  522 (17561 expanded)
%              Number of equality atoms :    4 ( 894 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3,X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X2))
                 => ( X5 = X4
                   => ( ( r1_lattice3(X1,X3,X4)
                       => r1_lattice3(X2,X3,X5) )
                      & ( r2_lattice3(X1,X3,X4)
                       => r2_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_yellow_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3,X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X2))
                   => ( X5 = X4
                     => ( ( r1_lattice3(X1,X3,X4)
                         => r1_lattice3(X2,X3,X5) )
                        & ( r2_lattice3(X1,X3,X4)
                         => r2_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_yellow_0])).

fof(c_0_7,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X16)
        | r1_orders_2(X15,X18,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X16)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,esk2_3(X15,X16,X17),X17)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_orders_2(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v4_yellow_0(esk4_0,esk3_0)
    & m1_yellow_0(esk4_0,esk3_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & esk7_0 = esk6_0
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
      | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r1_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X11)
        | r1_orders_2(X10,X12,X13)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X12),u1_struct_0(X10))
        | r1_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r1_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,X12,esk1_3(X10,X11,X12))
        | r1_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X7,X6)
        | r2_hidden(X7,X6)
        | v1_xboole_0(X6) )
      & ( ~ r2_hidden(X7,X6)
        | m1_subset_1(X7,X6)
        | v1_xboole_0(X6) )
      & ( ~ m1_subset_1(X7,X6)
        | v1_xboole_0(X7)
        | ~ v1_xboole_0(X6) )
      & ( ~ v1_xboole_0(X7)
        | m1_subset_1(X7,X6)
        | ~ v1_xboole_0(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( esk7_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21]),
    [final]).

fof(c_0_29,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

fof(c_0_38,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_12]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk3_0,u1_struct_0(esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk3_0,u1_struct_0(esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_lattice3(esk3_0,X2,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk2_3(esk3_0,X2,esk6_0),X2)
    | m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk6_0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r1_lattice3(esk3_0,X2,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),X2)
    | m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(X1),esk6_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(X1),esk6_0),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_26]),
    [final]).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk6_0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(X1),esk6_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(X1),esk6_0),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,u1_struct_0(esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_39]),
    [final]).

cnf(c_0_54,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,u1_struct_0(esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_39]),
    [final]).

cnf(c_0_56,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_12]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_lattice3(esk3_0,X2,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),X2)
    | m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_26]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_lattice3(esk3_0,X2,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,X2,esk6_0),X2)
    | m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_26]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_12]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_34]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(u1_struct_0(esk4_0),esk6_0) ),
    inference(ef,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(u1_struct_0(esk4_0),esk6_0) ),
    inference(ef,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,X1) ),
    inference(ef,[status(thm)],[c_0_46]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk6_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_34]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,X1) ),
    inference(ef,[status(thm)],[c_0_48]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(X1),esk6_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(X1),esk6_0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk6_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_36]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(X1),esk6_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(X1),esk6_0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_50]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_12]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_12]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_78,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_79,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_83,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_46]),c_0_33]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(u1_struct_0(esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_46]),c_0_43]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(u1_struct_0(esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_41]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_59]),c_0_35]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_35]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_61]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_44]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_62]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(u1_struct_0(esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_41]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_45]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_63]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_64]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(u1_struct_0(esk4_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_65]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_26]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(u1_struct_0(esk4_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_66]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_67]),
    [final]).

cnf(c_0_99,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)
    | m1_subset_1(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_36]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_68]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(X1,esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_69]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(X1,esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_72]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_73]),
    [final]).

cnf(c_0_107,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_75]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_20]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20]),
    [final]).

cnf(c_0_112,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20]),
    [final]).

cnf(c_0_113,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_77]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_20]),
    [final]).

cnf(c_0_115,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_116,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_117,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_20]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_20]),
    [final]).

cnf(c_0_119,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_20]),
    [final]).

cnf(c_0_120,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_20]),
    [final]).

cnf(c_0_121,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12]),
    [final]).

cnf(c_0_122,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_123,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_80,c_0_15]),
    [final]).

cnf(c_0_124,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_15]),
    [final]).

cnf(c_0_125,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_15]),c_0_15]),
    [final]).

cnf(c_0_126,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_127,negated_conjecture,
    ( m1_yellow_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_128,negated_conjecture,
    ( v4_yellow_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:30:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.15/0.39  # and selection function SelectNewComplexAHP.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.027 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # No proof found!
% 0.15/0.39  # SZS status CounterSatisfiable
% 0.15/0.39  # SZS output start Saturation
% 0.15/0.39  fof(t62_yellow_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3, X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X5=X4=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X2,X3,X5))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X2,X3,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_yellow_0)).
% 0.15/0.39  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.15/0.39  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.15/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.15/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.15/0.39  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.15/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3, X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X5=X4=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X2,X3,X5))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X2,X3,X5))))))))), inference(assume_negation,[status(cth)],[t62_yellow_0])).
% 0.15/0.39  fof(c_0_7, plain, ![X15, X16, X17, X18]:((~r2_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X16)|r1_orders_2(X15,X18,X17)))|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((r2_hidden(esk2_3(X15,X16,X17),X16)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&(~r1_orders_2(X15,esk2_3(X15,X16,X17),X17)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.15/0.39  fof(c_0_8, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_orders_2(esk3_0))&(((~v2_struct_0(esk4_0)&v4_yellow_0(esk4_0,esk3_0))&m1_yellow_0(esk4_0,esk3_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(esk7_0=esk6_0&(((r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0))&(~r2_lattice3(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)))&((r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0))&(~r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).
% 0.15/0.39  fof(c_0_9, plain, ![X10, X11, X12, X13]:((~r1_lattice3(X10,X11,X12)|(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_hidden(X13,X11)|r1_orders_2(X10,X12,X13)))|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&((m1_subset_1(esk1_3(X10,X11,X12),u1_struct_0(X10))|r1_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&((r2_hidden(esk1_3(X10,X11,X12),X11)|r1_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&(~r1_orders_2(X10,X12,esk1_3(X10,X11,X12))|r1_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.15/0.39  fof(c_0_10, plain, ![X6, X7]:(((~m1_subset_1(X7,X6)|r2_hidden(X7,X6)|v1_xboole_0(X6))&(~r2_hidden(X7,X6)|m1_subset_1(X7,X6)|v1_xboole_0(X6)))&((~m1_subset_1(X7,X6)|v1_xboole_0(X7)|~v1_xboole_0(X6))&(~v1_xboole_0(X7)|m1_subset_1(X7,X6)|~v1_xboole_0(X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.15/0.39  cnf(c_0_11, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.15/0.39  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.15/0.39  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.15/0.39  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.39  cnf(c_0_15, negated_conjecture, (esk7_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.15/0.39  cnf(c_0_16, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.15/0.39  cnf(c_0_17, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.15/0.39  cnf(c_0_18, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), ['final']).
% 0.15/0.39  cnf(c_0_19, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.15/0.39  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_14, c_0_15]), ['final']).
% 0.15/0.39  cnf(c_0_21, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_12]), c_0_13])]), ['final']).
% 0.15/0.39  cnf(c_0_22, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.15/0.39  cnf(c_0_23, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.15/0.39  cnf(c_0_24, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.15/0.39  cnf(c_0_25, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.15/0.39  cnf(c_0_26, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.15/0.39  cnf(c_0_27, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_28, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_21]), ['final']).
% 0.15/0.39  fof(c_0_29, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.15/0.39  cnf(c_0_30, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|~r2_lattice3(esk3_0,X2,X1)|~r2_hidden(esk6_0,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_12]), c_0_13])]), ['final']).
% 0.15/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_32, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X2,X1)|~r2_hidden(esk6_0,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_12]), c_0_13])]), ['final']).
% 0.15/0.39  cnf(c_0_33, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.15/0.39  cnf(c_0_34, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_26]), ['final']).
% 0.15/0.39  cnf(c_0_35, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_25, c_0_28]), ['final']).
% 0.15/0.39  cnf(c_0_36, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.15/0.39  cnf(c_0_37, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.15/0.39  fof(c_0_38, plain, ![X9]:(~l1_orders_2(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.15/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_12]), ['final']).
% 0.15/0.39  cnf(c_0_40, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|v1_xboole_0(u1_struct_0(esk4_0))|~r2_lattice3(esk3_0,u1_struct_0(esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_31]), ['final']).
% 0.15/0.39  cnf(c_0_41, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X2,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_25, c_0_28]), ['final']).
% 0.15/0.39  cnf(c_0_42, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))|~r1_lattice3(esk3_0,u1_struct_0(esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_31]), ['final']).
% 0.15/0.39  cnf(c_0_43, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X2,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.15/0.39  cnf(c_0_44, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_34]), ['final']).
% 0.15/0.39  cnf(c_0_45, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.15/0.39  cnf(c_0_46, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_lattice3(esk3_0,X2,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk2_3(esk3_0,X2,esk6_0),X2)|m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_26]), ['final']).
% 0.15/0.39  cnf(c_0_47, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk6_0,X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_34]), ['final']).
% 0.15/0.39  cnf(c_0_48, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r1_lattice3(esk3_0,X2,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),X2)|m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_28]), ['final']).
% 0.15/0.39  cnf(c_0_49, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(X1),esk6_0)|v2_struct_0(X1)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(X1),esk6_0),u1_struct_0(X1))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_37, c_0_26]), ['final']).
% 0.15/0.39  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.15/0.39  cnf(c_0_51, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk6_0,X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_36]), ['final']).
% 0.15/0.39  cnf(c_0_52, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(X1),esk6_0)|v2_struct_0(X1)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(X1),esk6_0),u1_struct_0(X1))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_37, c_0_28]), ['final']).
% 0.15/0.39  cnf(c_0_53, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|v1_xboole_0(u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,u1_struct_0(esk3_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_39]), ['final']).
% 0.15/0.39  cnf(c_0_54, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.15/0.39  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|v1_xboole_0(u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,u1_struct_0(esk3_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_39]), ['final']).
% 0.15/0.39  cnf(c_0_56, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.15/0.39  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))|~r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_12]), ['final']).
% 0.15/0.39  cnf(c_0_58, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_lattice3(esk3_0,X2,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),X2)|m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_26]), ['final']).
% 0.15/0.39  cnf(c_0_59, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_lattice3(esk3_0,X2,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,X2,esk6_0),X2)|m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_26]), ['final']).
% 0.15/0.39  cnf(c_0_60, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))|~r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_12]), ['final']).
% 0.15/0.39  cnf(c_0_61, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_34]), ['final']).
% 0.15/0.39  cnf(c_0_62, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_36]), ['final']).
% 0.15/0.39  cnf(c_0_63, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_34]), ['final']).
% 0.15/0.39  cnf(c_0_64, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_34]), ['final']).
% 0.15/0.39  cnf(c_0_65, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(u1_struct_0(esk4_0),esk6_0)), inference(ef,[status(thm)],[c_0_44]), ['final']).
% 0.15/0.39  cnf(c_0_66, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(u1_struct_0(esk4_0),esk6_0)), inference(ef,[status(thm)],[c_0_45]), ['final']).
% 0.15/0.39  cnf(c_0_67, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,X1)), inference(ef,[status(thm)],[c_0_46]), ['final']).
% 0.15/0.39  cnf(c_0_68, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk6_0,esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_34]), ['final']).
% 0.15/0.39  cnf(c_0_69, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,X1)), inference(ef,[status(thm)],[c_0_48]), ['final']).
% 0.15/0.39  cnf(c_0_70, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.15/0.39  cnf(c_0_71, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(X1),esk6_0)|v2_struct_0(X1)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(X1),esk6_0),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50]), ['final']).
% 0.15/0.39  cnf(c_0_72, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk6_0,esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_36]), ['final']).
% 0.15/0.39  cnf(c_0_73, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(X1),esk6_0)|v2_struct_0(X1)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(X1),esk6_0),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_52, c_0_50]), ['final']).
% 0.15/0.39  cnf(c_0_74, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_53, c_0_12]), ['final']).
% 0.15/0.39  cnf(c_0_75, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_12]), c_0_13])]), ['final']).
% 0.15/0.39  cnf(c_0_76, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_12]), ['final']).
% 0.15/0.39  cnf(c_0_77, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_12]), c_0_13])]), ['final']).
% 0.15/0.39  cnf(c_0_78, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.15/0.39  cnf(c_0_79, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.15/0.39  cnf(c_0_80, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.39  cnf(c_0_81, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.39  cnf(c_0_82, negated_conjecture, (~r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.39  cnf(c_0_83, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_46]), c_0_33]), ['final']).
% 0.15/0.39  cnf(c_0_84, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(u1_struct_0(esk4_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_46]), c_0_43]), ['final']).
% 0.15/0.39  cnf(c_0_85, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(u1_struct_0(esk4_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_41]), ['final']).
% 0.15/0.39  cnf(c_0_86, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_59]), c_0_35]), ['final']).
% 0.15/0.39  cnf(c_0_87, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_48]), c_0_35]), ['final']).
% 0.15/0.39  cnf(c_0_88, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk6_0,X1)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_61]), ['final']).
% 0.15/0.39  cnf(c_0_89, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_44]), ['final']).
% 0.15/0.39  cnf(c_0_90, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk6_0,X1)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_62]), ['final']).
% 0.15/0.39  cnf(c_0_91, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(u1_struct_0(esk4_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_48]), c_0_41]), ['final']).
% 0.15/0.39  cnf(c_0_92, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_45]), ['final']).
% 0.15/0.39  cnf(c_0_93, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk6_0,X1)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_63]), ['final']).
% 0.15/0.39  cnf(c_0_94, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_64]), ['final']).
% 0.15/0.39  cnf(c_0_95, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(u1_struct_0(esk4_0),esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_65]), ['final']).
% 0.15/0.39  cnf(c_0_96, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_26]), ['final']).
% 0.15/0.39  cnf(c_0_97, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(u1_struct_0(esk4_0),esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_66]), ['final']).
% 0.15/0.39  cnf(c_0_98, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_67]), ['final']).
% 0.15/0.39  cnf(c_0_99, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),X1)|m1_subset_1(X1,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_36]), ['final']).
% 0.15/0.39  cnf(c_0_100, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_68]), ['final']).
% 0.15/0.39  cnf(c_0_101, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(X1,esk6_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_34]), ['final']).
% 0.15/0.39  cnf(c_0_102, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_69]), ['final']).
% 0.15/0.39  cnf(c_0_103, negated_conjecture, (r2_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_70, c_0_71]), ['final']).
% 0.15/0.39  cnf(c_0_104, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(X1,esk6_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_36]), ['final']).
% 0.15/0.39  cnf(c_0_105, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_72]), ['final']).
% 0.15/0.39  cnf(c_0_106, negated_conjecture, (r1_lattice3(esk3_0,u1_struct_0(esk4_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_70, c_0_73]), ['final']).
% 0.15/0.39  cnf(c_0_107, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_74, c_0_75]), ['final']).
% 0.15/0.39  cnf(c_0_108, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_75]), ['final']).
% 0.15/0.39  cnf(c_0_109, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_76, c_0_77]), ['final']).
% 0.15/0.39  cnf(c_0_110, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_111, negated_conjecture, (r1_orders_2(esk4_0,X1,esk6_0)|~r1_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~r2_hidden(esk6_0,X2)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_112, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,X1)|~r2_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~r2_hidden(esk6_0,X2)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_113, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_77]), ['final']).
% 0.15/0.39  cnf(c_0_114, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_115, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_12]), c_0_13])]), ['final']).
% 0.15/0.39  cnf(c_0_116, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_12]), c_0_13])]), ['final']).
% 0.15/0.39  cnf(c_0_117, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_118, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_119, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|~r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_78, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_120, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|~r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_79, c_0_20]), ['final']).
% 0.15/0.39  cnf(c_0_121, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_12]), ['final']).
% 0.15/0.39  cnf(c_0_122, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.15/0.39  cnf(c_0_123, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_80, c_0_15]), ['final']).
% 0.15/0.39  cnf(c_0_124, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_81, c_0_15]), ['final']).
% 0.15/0.39  cnf(c_0_125, negated_conjecture, (~r2_lattice3(esk4_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_15]), c_0_15]), ['final']).
% 0.15/0.39  cnf(c_0_126, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.15/0.39  cnf(c_0_127, negated_conjecture, (m1_yellow_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.15/0.39  cnf(c_0_128, negated_conjecture, (v4_yellow_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.15/0.39  # SZS output end Saturation
% 0.15/0.39  # Proof object total steps             : 129
% 0.15/0.39  # Proof object clause steps            : 116
% 0.15/0.39  # Proof object formula steps           : 13
% 0.15/0.39  # Proof object conjectures             : 105
% 0.15/0.39  # Proof object clause conjectures      : 102
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 26
% 0.15/0.39  # Proof object initial formulas used   : 6
% 0.15/0.39  # Proof object generating inferences   : 86
% 0.15/0.39  # Proof object simplifying inferences  : 27
% 0.15/0.39  # Parsed axioms                        : 6
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 26
% 0.15/0.39  # Removed in clause preprocessing      : 0
% 0.15/0.39  # Initial clauses in saturation        : 26
% 0.15/0.39  # Processed clauses                    : 174
% 0.15/0.39  # ...of these trivial                  : 0
% 0.15/0.39  # ...subsumed                          : 36
% 0.15/0.39  # ...remaining for further processing  : 138
% 0.15/0.39  # Other redundant clauses eliminated   : 0
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 0
% 0.15/0.39  # Backward-rewritten                   : 0
% 0.15/0.39  # Generated clauses                    : 130
% 0.15/0.39  # ...of the previous two non-trivial   : 122
% 0.15/0.39  # Contextual simplify-reflections      : 6
% 0.15/0.39  # Paramodulations                      : 118
% 0.15/0.39  # Factorizations                       : 12
% 0.15/0.39  # Equation resolutions                 : 0
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 112
% 0.15/0.39  #    Positive orientable unit clauses  : 6
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 2
% 0.15/0.39  #    Non-unit-clauses                  : 104
% 0.15/0.39  # Current number of unprocessed clauses: 0
% 0.15/0.39  # ...number of literals in the above   : 0
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 26
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 2608
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 499
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 42
% 0.15/0.39  # Unit Clause-clause subsumption calls : 0
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 0
% 0.15/0.39  # BW rewrite match successes           : 0
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 5204
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.040 s
% 0.15/0.39  # System time              : 0.002 s
% 0.15/0.39  # Total time               : 0.042 s
% 0.15/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
