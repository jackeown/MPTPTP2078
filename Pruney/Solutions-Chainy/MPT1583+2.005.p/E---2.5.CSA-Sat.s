%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:38 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 330 expanded)
%              Number of clauses        :   55 ( 121 expanded)
%              Number of leaves         :    6 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  244 (2798 expanded)
%              Number of equality atoms :    4 ( 172 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

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
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,X7)
      | v1_xboole_0(X7)
      | r2_hidden(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

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
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_10,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_12,plain,(
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

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_16,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_21,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( esk7_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_11]),c_0_19])]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_11]),c_0_19])]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,u1_struct_0(esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_30,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | ~ r2_lattice3(esk3_0,u1_struct_0(esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26]),
    [final]).

cnf(c_0_32,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_28]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | ~ r1_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_11]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_11]),c_0_19])]),
    [final]).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | ~ r2_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_11]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_11]),c_0_19])]),
    [final]).

cnf(c_0_41,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_42,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_33]),c_0_34]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_11]),c_0_19])]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_11]),c_0_19])]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_28]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_11]),c_0_19])]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_11]),c_0_19])]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_28]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_28]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_24]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_24]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_24]),c_0_24]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( m1_yellow_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( v4_yellow_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.21/0.38  # and selection function SelectNewComplexAHP.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # No proof found!
% 0.21/0.38  # SZS status CounterSatisfiable
% 0.21/0.38  # SZS output start Saturation
% 0.21/0.38  fof(t62_yellow_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3, X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X5=X4=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X2,X3,X5))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X2,X3,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_yellow_0)).
% 0.21/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.21/0.38  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.21/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.21/0.38  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.21/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3, X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X5=X4=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X2,X3,X5))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X2,X3,X5))))))))), inference(assume_negation,[status(cth)],[t62_yellow_0])).
% 0.21/0.38  fof(c_0_7, plain, ![X6, X7]:(~m1_subset_1(X6,X7)|(v1_xboole_0(X7)|r2_hidden(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.38  fof(c_0_8, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_orders_2(esk3_0))&(((~v2_struct_0(esk4_0)&v4_yellow_0(esk4_0,esk3_0))&m1_yellow_0(esk4_0,esk3_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(esk7_0=esk6_0&(((r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0))&(~r2_lattice3(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)))&((r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0))&(~r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).
% 0.21/0.38  fof(c_0_9, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.21/0.38  cnf(c_0_10, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.21/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  fof(c_0_12, plain, ![X10, X11, X12, X13]:((~r1_lattice3(X10,X11,X12)|(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_hidden(X13,X11)|r1_orders_2(X10,X12,X13)))|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&((m1_subset_1(esk1_3(X10,X11,X12),u1_struct_0(X10))|r1_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&((r2_hidden(esk1_3(X10,X11,X12),X11)|r1_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&(~r1_orders_2(X10,X12,esk1_3(X10,X11,X12))|r1_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.21/0.38  cnf(c_0_13, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.21/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.21/0.38  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  fof(c_0_16, plain, ![X9]:(~l1_orders_2(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.21/0.38  fof(c_0_17, plain, ![X15, X16, X17, X18]:((~r2_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X16)|r1_orders_2(X15,X18,X17)))|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((r2_hidden(esk2_3(X15,X16,X17),X16)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&(~r1_orders_2(X15,esk2_3(X15,X16,X17),X17)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.21/0.38  cnf(c_0_18, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.38  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk3_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.21/0.38  cnf(c_0_21, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.21/0.38  cnf(c_0_22, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_24, negated_conjecture, (esk7_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X2,X1)|~r2_hidden(esk6_0,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_11]), c_0_19])]), ['final']).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_19])]), ['final']).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|~r2_lattice3(esk3_0,X2,X1)|~r2_hidden(esk6_0,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_11]), c_0_19])]), ['final']).
% 0.21/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_23, c_0_24]), ['final']).
% 0.21/0.38  cnf(c_0_29, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,u1_struct_0(esk3_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.21/0.38  cnf(c_0_30, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|~r2_lattice3(esk3_0,u1_struct_0(esk3_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_26]), ['final']).
% 0.21/0.38  cnf(c_0_32, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_10, c_0_28]), ['final']).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  cnf(c_0_35, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|~r1_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_11]), ['final']).
% 0.21/0.38  cnf(c_0_37, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_11]), c_0_19])]), ['final']).
% 0.21/0.38  cnf(c_0_38, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|~r2_lattice3(esk3_0,u1_struct_0(esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_11]), ['final']).
% 0.21/0.38  cnf(c_0_40, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_11]), c_0_19])]), ['final']).
% 0.21/0.38  cnf(c_0_41, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.38  cnf(c_0_42, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_33]), c_0_34]), ['final']).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_46, negated_conjecture, (~r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_11]), c_0_19])]), ['final']).
% 0.21/0.38  cnf(c_0_48, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_36, c_0_37]), ['final']).
% 0.21/0.38  cnf(c_0_49, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_11]), c_0_19])]), ['final']).
% 0.21/0.38  cnf(c_0_50, negated_conjecture, (r1_orders_2(esk4_0,X1,esk6_0)|~r1_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~r2_hidden(esk6_0,X2)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_28]), ['final']).
% 0.21/0.38  cnf(c_0_51, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_28]), ['final']).
% 0.21/0.38  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_40]), ['final']).
% 0.21/0.38  cnf(c_0_53, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_28]), ['final']).
% 0.21/0.38  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,X1)|~r2_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~r2_hidden(esk6_0,X2)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_28]), ['final']).
% 0.21/0.38  cnf(c_0_55, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_11]), c_0_19])]), ['final']).
% 0.21/0.38  cnf(c_0_56, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_28]), ['final']).
% 0.21/0.38  cnf(c_0_57, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_28]), ['final']).
% 0.21/0.38  cnf(c_0_58, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_11]), c_0_19])]), ['final']).
% 0.21/0.38  cnf(c_0_59, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|~r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_28]), ['final']).
% 0.21/0.38  cnf(c_0_60, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|~r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_28]), ['final']).
% 0.21/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_21]), ['final']).
% 0.21/0.38  cnf(c_0_62, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_44, c_0_24]), ['final']).
% 0.21/0.38  cnf(c_0_63, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_45, c_0_24]), ['final']).
% 0.21/0.38  cnf(c_0_64, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  cnf(c_0_65, negated_conjecture, (~r2_lattice3(esk4_0,esk5_0,esk6_0)|~r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_24]), c_0_24]), ['final']).
% 0.21/0.38  cnf(c_0_66, negated_conjecture, (m1_yellow_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  cnf(c_0_67, negated_conjecture, (v4_yellow_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  # SZS output end Saturation
% 0.21/0.38  # Proof object total steps             : 68
% 0.21/0.38  # Proof object clause steps            : 55
% 0.21/0.38  # Proof object formula steps           : 13
% 0.21/0.38  # Proof object conjectures             : 47
% 0.21/0.38  # Proof object clause conjectures      : 44
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 23
% 0.21/0.38  # Proof object initial formulas used   : 6
% 0.21/0.38  # Proof object generating inferences   : 28
% 0.21/0.38  # Proof object simplifying inferences  : 25
% 0.21/0.38  # Parsed axioms                        : 6
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 23
% 0.21/0.38  # Removed in clause preprocessing      : 0
% 0.21/0.38  # Initial clauses in saturation        : 23
% 0.21/0.38  # Processed clauses                    : 74
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 74
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 2
% 0.21/0.38  # Generated clauses                    : 28
% 0.21/0.38  # ...of the previous two non-trivial   : 28
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 28
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 0
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 49
% 0.21/0.38  #    Positive orientable unit clauses  : 7
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 40
% 0.21/0.38  # Current number of unprocessed clauses: 0
% 0.21/0.38  # ...number of literals in the above   : 0
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 25
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 182
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 49
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.38  # Unit Clause-clause subsumption calls : 0
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 1
% 0.21/0.38  # BW rewrite match successes           : 1
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 2443
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.030 s
% 0.21/0.38  # System time              : 0.004 s
% 0.21/0.38  # Total time               : 0.034 s
% 0.21/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
