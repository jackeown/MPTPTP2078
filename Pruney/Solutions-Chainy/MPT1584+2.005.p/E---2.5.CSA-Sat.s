%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:38 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  122 (2654 expanded)
%              Number of clauses        :  113 (1021 expanded)
%              Number of leaves         :    4 ( 617 expanded)
%              Depth                    :   10
%              Number of atoms          :  459 (22601 expanded)
%              Number of equality atoms :    4 (1211 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( X5 = X4
                       => ( ( r1_lattice3(X2,X3,X5)
                           => r1_lattice3(X1,X3,X4) )
                          & ( r2_lattice3(X2,X3,X5)
                           => r2_lattice3(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_yellow_0)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ( X5 = X4
                         => ( ( r1_lattice3(X2,X3,X5)
                             => r1_lattice3(X1,X3,X4) )
                            & ( r2_lattice3(X2,X3,X5)
                             => r2_lattice3(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_yellow_0])).

fof(c_0_5,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X17,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,esk2_3(X14,X15,X16),X16)
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_orders_2(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_yellow_0(esk4_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & esk7_0 = esk6_0
    & ( r2_lattice3(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk3_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( r2_lattice3(esk4_0,esk5_0,esk7_0)
      | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk3_0,esk5_0,esk6_0)
      | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

fof(c_0_7,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X12,X10)
        | r1_orders_2(X9,X11,X12)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))
        | r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X10)
        | r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,X11,esk1_3(X9,X10,X11))
        | r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | r2_hidden(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_11])]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | r2_hidden(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_24]),c_0_11])]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_25]),c_0_11])]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_25]),c_0_11])]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_26]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_11])]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_24]),c_0_11])]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_11])]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_24]),c_0_11])]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_11])]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_25]),c_0_11])]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_29]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_11])]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_25]),c_0_11])]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_30]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_31]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_32]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_33]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_48,negated_conjecture,
    ( esk7_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_24]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_25]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_40]),c_0_24]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_25]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_43]),c_0_24]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_44]),c_0_25]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_45]),c_0_25]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_10])]),
    [final]).

cnf(c_0_60,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_61,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_21]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_21]),c_0_10])]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_48]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_48]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0)
    | r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_69,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_26]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_26]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_26]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_26]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_26]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_26]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_26]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_26]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_10])]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_22]),c_0_10])]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_10])]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_26]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_24]),c_0_11])]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),esk2_3(esk3_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_24]),c_0_11])]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | r2_hidden(esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_62]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | r2_hidden(esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_62]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_63]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_62]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_62]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( r1_orders_2(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_63]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_63]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | r2_hidden(esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_63]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_25]),c_0_11])]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0),esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_62]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),esk2_3(esk3_0,esk5_0,esk6_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0),esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_63]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),esk2_3(esk3_0,esk5_0,esk6_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_63]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_62]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),esk2_3(esk3_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_25]),c_0_11])]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_62]),
    [final]).

cnf(c_0_99,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_63]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_33]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_63]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_26]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_66]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ l1_orders_2(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_66]),
    [final]).

cnf(c_0_107,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_21]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_66]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_66]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_16]),
    [final]).

cnf(c_0_112,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_113,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_66]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_66]),
    [final]).

cnf(c_0_115,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_66]),
    [final]).

cnf(c_0_116,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_22]),
    [final]).

cnf(c_0_117,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_66]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk6_0)
    | r1_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_48]),c_0_48]),
    [final]).

cnf(c_0_119,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_120,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_121,negated_conjecture,
    ( m1_yellow_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(t63_yellow_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&m1_yellow_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X5=X4=>((r1_lattice3(X2,X3,X5)=>r1_lattice3(X1,X3,X4))&(r2_lattice3(X2,X3,X5)=>r2_lattice3(X1,X3,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_yellow_0)).
% 0.13/0.38  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.38  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&m1_yellow_0(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(X5=X4=>((r1_lattice3(X2,X3,X5)=>r1_lattice3(X1,X3,X4))&(r2_lattice3(X2,X3,X5)=>r2_lattice3(X1,X3,X4)))))))))), inference(assume_negation,[status(cth)],[t63_yellow_0])).
% 0.13/0.38  fof(c_0_5, plain, ![X14, X15, X16, X17]:((~r2_lattice3(X14,X15,X16)|(~m1_subset_1(X17,u1_struct_0(X14))|(~r2_hidden(X17,X15)|r1_orders_2(X14,X17,X16)))|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((r2_hidden(esk2_3(X14,X15,X16),X15)|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&(~r1_orders_2(X14,esk2_3(X14,X15,X16),X16)|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.38  fof(c_0_6, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_orders_2(esk3_0))&((~v2_struct_0(esk4_0)&m1_yellow_0(esk4_0,esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(esk7_0=esk6_0&(((r2_lattice3(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,esk5_0,esk7_0))&(~r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,esk5_0,esk7_0)))&((r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0))&(~r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0)))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).
% 0.13/0.38  fof(c_0_7, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.38  fof(c_0_8, plain, ![X9, X10, X11, X12]:((~r1_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X10)|r1_orders_2(X9,X11,X12)))|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))|r1_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((r2_hidden(esk1_3(X9,X10,X11),X10)|r1_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&(~r1_orders_2(X9,X11,esk1_3(X9,X10,X11))|r1_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.13/0.38  cnf(c_0_9, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_12, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (~r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_10]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_19, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_10]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_23, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_20, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_10]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_27, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_28, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|r2_hidden(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|r2_hidden(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_24]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_25]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_25]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_17, c_0_26]), ['final']).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_24]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (r1_orders_2(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_24]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_25]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_17, c_0_29]), ['final']).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (r1_orders_2(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_25]), c_0_11])]), ['final']).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_17, c_0_30]), ['final']).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_31]), ['final']).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_32]), ['final']).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_15, c_0_33]), ['final']).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (r1_lattice3(esk4_0,esk5_0,esk7_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (esk7_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_24]), ['final']).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_24]), ['final']).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_40]), c_0_24]), ['final']).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_43]), c_0_24]), ['final']).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_44]), c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_45]), c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_22]), c_0_10])]), ['final']).
% 0.19/0.38  cnf(c_0_60, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_61, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_21]), ['final']).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (r1_lattice3(esk4_0,esk5_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_47, c_0_48]), ['final']).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_21]), c_0_10])]), ['final']).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_49, c_0_48]), ['final']).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_50, c_0_48]), ['final']).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_55, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_57, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_16]), c_0_10])]), ['final']).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_22]), c_0_10])]), ['final']).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_10])]), ['final']).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_81, negated_conjecture, (r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_24]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),esk2_3(esk3_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_24]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|r2_hidden(esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_62]), ['final']).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|r2_hidden(esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_62]), ['final']).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, (r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_63]), ['final']).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, (r1_orders_2(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_27, c_0_62]), ['final']).
% 0.19/0.38  cnf(c_0_87, negated_conjecture, (r1_orders_2(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r1_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_28, c_0_62]), ['final']).
% 0.19/0.38  cnf(c_0_88, negated_conjecture, (r1_orders_2(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_27, c_0_63]), ['final']).
% 0.19/0.38  cnf(c_0_89, negated_conjecture, (r1_orders_2(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_28, c_0_63]), ['final']).
% 0.19/0.38  cnf(c_0_90, negated_conjecture, (r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|r2_hidden(esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_63]), ['final']).
% 0.19/0.38  cnf(c_0_91, negated_conjecture, (r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,esk2_3(esk3_0,esk5_0,esk6_0),esk1_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_25]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_92, negated_conjecture, (r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r1_orders_2(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0),esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_62]), ['final']).
% 0.19/0.38  cnf(c_0_93, negated_conjecture, (r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),esk2_3(esk3_0,esk5_0,esk6_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_62]), ['final']).
% 0.19/0.38  cnf(c_0_94, negated_conjecture, (r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0),esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_63]), ['final']).
% 0.19/0.38  cnf(c_0_95, negated_conjecture, (r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),esk2_3(esk3_0,esk5_0,esk6_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_63]), ['final']).
% 0.19/0.38  cnf(c_0_96, negated_conjecture, (r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_9, c_0_62]), ['final']).
% 0.19/0.38  cnf(c_0_97, negated_conjecture, (r2_lattice3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),esk2_3(esk3_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_25]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_98, negated_conjecture, (r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_62]), ['final']).
% 0.19/0.38  cnf(c_0_99, negated_conjecture, (r2_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk2_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_9, c_0_63]), ['final']).
% 0.19/0.38  cnf(c_0_100, negated_conjecture, (r1_orders_2(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk6_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_10]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_101, negated_conjecture, (r1_lattice3(esk4_0,esk5_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_33]), ['final']).
% 0.19/0.38  cnf(c_0_102, negated_conjecture, (r1_lattice3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk4_0,X1,esk2_3(esk3_0,esk5_0,esk6_0)),u1_struct_0(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_63]), ['final']).
% 0.19/0.38  cnf(c_0_103, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk6_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_65, c_0_26]), ['final']).
% 0.19/0.38  cnf(c_0_104, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(esk6_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_10]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_105, negated_conjecture, (r1_orders_2(esk4_0,X1,esk6_0)|~r1_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk6_0,X2)), inference(spm,[status(thm)],[c_0_28, c_0_66]), ['final']).
% 0.19/0.38  cnf(c_0_106, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,X1)|~r2_lattice3(esk4_0,X2,X1)|~l1_orders_2(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk6_0,X2)), inference(spm,[status(thm)],[c_0_27, c_0_66]), ['final']).
% 0.19/0.38  cnf(c_0_107, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_21]), ['final']).
% 0.19/0.38  cnf(c_0_108, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk2_3(esk4_0,X1,esk6_0),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_66]), ['final']).
% 0.19/0.38  cnf(c_0_109, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|r2_hidden(esk1_3(esk4_0,X1,esk6_0),X1)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_66]), ['final']).
% 0.19/0.38  cnf(c_0_110, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk2_3(esk3_0,X1,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_10]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_111, negated_conjecture, (r1_lattice3(esk4_0,esk5_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_16]), ['final']).
% 0.19/0.38  cnf(c_0_112, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_10]), c_0_11])]), ['final']).
% 0.19/0.38  cnf(c_0_113, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk2_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_9, c_0_66]), ['final']).
% 0.19/0.38  cnf(c_0_114, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|m1_subset_1(esk1_3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_66]), ['final']).
% 0.19/0.38  cnf(c_0_115, negated_conjecture, (r2_lattice3(esk4_0,X1,esk6_0)|~r1_orders_2(esk4_0,esk2_3(esk4_0,X1,esk6_0),esk6_0)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_66]), ['final']).
% 0.19/0.38  cnf(c_0_116, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_117, negated_conjecture, (r1_lattice3(esk4_0,X1,esk6_0)|~r1_orders_2(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk6_0))|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_66]), ['final']).
% 0.19/0.38  cnf(c_0_118, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk6_0)|r1_lattice3(esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_48]), c_0_48]), ['final']).
% 0.19/0.38  cnf(c_0_119, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_120, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_121, negated_conjecture, (m1_yellow_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  # SZS output end Saturation
% 0.19/0.38  # Proof object total steps             : 122
% 0.19/0.38  # Proof object clause steps            : 113
% 0.19/0.38  # Proof object formula steps           : 9
% 0.19/0.38  # Proof object conjectures             : 107
% 0.19/0.38  # Proof object clause conjectures      : 104
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 21
% 0.19/0.38  # Proof object initial formulas used   : 4
% 0.19/0.38  # Proof object generating inferences   : 88
% 0.19/0.38  # Proof object simplifying inferences  : 71
% 0.19/0.38  # Parsed axioms                        : 4
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 21
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 21
% 0.19/0.38  # Processed clauses                    : 144
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 14
% 0.19/0.38  # ...remaining for further processing  : 130
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 102
% 0.19/0.38  # ...of the previous two non-trivial   : 102
% 0.19/0.38  # Contextual simplify-reflections      : 8
% 0.19/0.38  # Paramodulations                      : 102
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 109
% 0.19/0.38  #    Positive orientable unit clauses  : 6
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 101
% 0.19/0.38  # Current number of unprocessed clauses: 0
% 0.19/0.38  # ...number of literals in the above   : 0
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 21
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2384
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 750
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 22
% 0.19/0.38  # Unit Clause-clause subsumption calls : 2
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5558
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.040 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
