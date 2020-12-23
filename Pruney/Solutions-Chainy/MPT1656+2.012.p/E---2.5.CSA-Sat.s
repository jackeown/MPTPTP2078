%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:21 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 973 expanded)
%              Number of clauses        :   51 ( 349 expanded)
%              Number of leaves         :    5 ( 232 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 (6672 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattice3(X1,X2,X3)
              <=> r1_lattice3(X1,k4_waybel_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_0)).

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

fof(t4_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
               => ! [X4] :
                    ( ( r1_lattice3(X1,X4,X3)
                     => r1_lattice3(X1,X4,X2) )
                    & ( r2_lattice3(X1,X4,X2)
                     => r2_lattice3(X1,X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X3)
                <=> r1_lattice3(X1,k4_waybel_0(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_waybel_0])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_hidden(X10,X8)
        | r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))
        | r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X9,esk1_3(X7,X8,X9))
        | r1_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & ( ~ r1_lattice3(esk3_0,esk4_0,esk5_0)
      | ~ r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0) )
    & ( r1_lattice3(esk3_0,esk4_0,esk5_0)
      | r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X13)
        | r1_orders_2(X12,X15,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))
        | r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,esk2_3(X12,X13,X14),X14)
        | r2_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_12,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_lattice3(esk3_0,esk4_0,esk5_0)
    | ~ r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk5_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_15,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

fof(c_0_18,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r1_lattice3(X17,X20,X19)
        | r1_lattice3(X17,X20,X18)
        | ~ r1_orders_2(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v4_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r2_lattice3(X17,X20,X18)
        | r2_lattice3(X17,X20,X19)
        | ~ r1_orders_2(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v4_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,X2,esk5_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14]),
    [final]).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_22,plain,
    ( r1_lattice3(X1,X2,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,esk5_0),X1)
    | r1_lattice3(esk3_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_26,plain,
    ( r2_lattice3(X1,X2,X4)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_20]),c_0_11])]),
    [final]).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | m1_subset_1(esk1_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,X2,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_14]),c_0_23]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)
    | r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk5_0)
    | m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23]),c_0_11])]),c_0_20]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk5_0)
    | ~ r2_hidden(esk5_0,X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_10]),c_0_11])]),
    [final]).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ v3_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | r1_orders_2(X5,X6,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)
    | m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_14]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk5_0)
    | r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_10])]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | m1_subset_1(esk2_3(esk3_0,X2,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_27]),c_0_11])]),c_0_20]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_20]),c_0_11])]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk5_0,X1)
    | ~ r1_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_20]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_11])]),
    [final]).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk5_0)
    | r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)
    | r1_lattice3(esk3_0,X1,X2)
    | m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,X2,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_34]),c_0_23]),c_0_11])]),c_0_14]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk5_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_35]),c_0_23]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)
    | r1_orders_2(esk3_0,X1,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,X2,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_35]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_10]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | m1_subset_1(esk1_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,X2,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_37]),c_0_23]),c_0_11])]),c_0_20]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk5_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | m1_subset_1(esk2_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,esk5_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_23]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | r2_hidden(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),X1)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_20]),c_0_11])]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),X1)
    | r1_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_11])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk5_0)
    | r2_hidden(esk2_3(esk3_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_20]),c_0_11]),c_0_42])]),c_0_43]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),X1)
    | r1_lattice3(esk3_0,esk4_0,esk5_0)
    | ~ r1_orders_2(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_44]),c_0_23]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_58,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_59,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_10]),c_0_11]),c_0_42])]),c_0_43]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:53:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S047A
% 0.14/0.38  # and selection function PSelectComplexPreferNEQ.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(t36_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>r1_lattice3(X1,k4_waybel_0(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_waybel_0)).
% 0.14/0.38  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.14/0.38  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.14/0.38  fof(t4_yellow_0, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>![X4]:((r1_lattice3(X1,X4,X3)=>r1_lattice3(X1,X4,X2))&(r2_lattice3(X1,X4,X2)=>r2_lattice3(X1,X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_0)).
% 0.14/0.38  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.14/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>r1_lattice3(X1,k4_waybel_0(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t36_waybel_0])).
% 0.14/0.38  fof(c_0_6, plain, ![X7, X8, X9, X10]:((~r1_lattice3(X7,X8,X9)|(~m1_subset_1(X10,u1_struct_0(X7))|(~r2_hidden(X10,X8)|r1_orders_2(X7,X9,X10)))|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&((m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))|r1_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&((r2_hidden(esk1_3(X7,X8,X9),X8)|r1_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&(~r1_orders_2(X7,X9,esk1_3(X7,X8,X9))|r1_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&((~r1_lattice3(esk3_0,esk4_0,esk5_0)|~r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))&(r1_lattice3(esk3_0,esk4_0,esk5_0)|r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X12, X13, X14, X15]:((~r2_lattice3(X12,X13,X14)|(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_hidden(X15,X13)|r1_orders_2(X12,X15,X14)))|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&((m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))|r2_lattice3(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&((r2_hidden(esk2_3(X12,X13,X14),X13)|r2_lattice3(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&(~r1_orders_2(X12,esk2_3(X12,X13,X14),X14)|r2_lattice3(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.14/0.38  cnf(c_0_9, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.14/0.38  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_12, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (~r1_lattice3(esk3_0,esk4_0,esk5_0)|~r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (r1_lattice3(esk3_0,X1,esk5_0)|m1_subset_1(esk1_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_15, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (r2_lattice3(esk3_0,X1,esk5_0)|m1_subset_1(esk2_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_10]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.14/0.38  fof(c_0_18, plain, ![X17, X18, X19, X20]:((~r1_lattice3(X17,X20,X19)|r1_lattice3(X17,X20,X18)|~r1_orders_2(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(~v4_orders_2(X17)|~l1_orders_2(X17)))&(~r2_lattice3(X17,X20,X18)|r2_lattice3(X17,X20,X19)|~r1_orders_2(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(~v4_orders_2(X17)|~l1_orders_2(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (r1_orders_2(esk3_0,X1,esk5_0)|m1_subset_1(esk2_3(esk3_0,X2,esk5_0),u1_struct_0(esk3_0))|~r2_hidden(X1,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_10]), c_0_11])]), ['final']).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.14/0.38  cnf(c_0_22, plain, (r1_lattice3(X1,X2,X4)|~r1_lattice3(X1,X2,X3)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk5_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk2_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_3(esk3_0,X1,esk5_0),X1)|r1_lattice3(esk3_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_10]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_26, plain, (r2_lattice3(X1,X2,X4)|~r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (r2_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_20]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_28, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.38  cnf(c_0_29, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|m1_subset_1(esk1_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,X2,esk5_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_14]), c_0_23]), c_0_10]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)|r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk5_0)|m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23]), c_0_11])]), c_0_20]), ['final']).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (r1_orders_2(esk3_0,X1,esk5_0)|~r2_hidden(esk5_0,X2)|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_10]), c_0_11])]), ['final']).
% 0.21/0.38  fof(c_0_33, plain, ![X5, X6]:(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|r1_orders_2(X5,X6,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (r1_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)|m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_14]), ['final']).
% 0.21/0.38  cnf(c_0_35, negated_conjecture, (r2_lattice3(esk3_0,X1,esk5_0)|r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_30]), c_0_10])]), ['final']).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (r1_orders_2(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|m1_subset_1(esk2_3(esk3_0,X2,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r2_hidden(X1,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_27]), c_0_11])]), c_0_20]), ['final']).
% 0.21/0.38  cnf(c_0_37, negated_conjecture, (r1_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|m1_subset_1(esk1_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_20]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk5_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r2_hidden(esk5_0,X1)|~r1_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_20]), ['final']).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (r1_orders_2(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),X2)|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_40, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  cnf(c_0_41, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.21/0.38  cnf(c_0_42, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, (r1_lattice3(esk3_0,esk4_0,esk5_0)|r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)|r1_lattice3(esk3_0,X1,X2)|m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,X2,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_34]), c_0_23]), c_0_11])]), c_0_14]), ['final']).
% 0.21/0.38  cnf(c_0_46, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,esk5_0,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_35]), c_0_23]), c_0_10]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)|r1_orders_2(esk3_0,X1,esk5_0)|m1_subset_1(esk2_3(esk3_0,X2,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk2_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r2_hidden(X1,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_35]), c_0_10]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_48, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|m1_subset_1(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_10]), ['final']).
% 0.21/0.38  cnf(c_0_49, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|m1_subset_1(esk1_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,X2,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_37]), c_0_23]), c_0_11])]), c_0_20]), ['final']).
% 0.21/0.38  cnf(c_0_50, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk5_0)|m1_subset_1(esk1_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_37]), ['final']).
% 0.21/0.38  cnf(c_0_51, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|m1_subset_1(esk2_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,esk5_0,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16]), c_0_23]), c_0_10]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_52, negated_conjecture, (r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_25]), ['final']).
% 0.21/0.38  cnf(c_0_53, negated_conjecture, (r2_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|r2_hidden(esk2_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),X1)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_20]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0)),X1)|r1_lattice3(esk3_0,X1,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_55, negated_conjecture, (r2_lattice3(esk3_0,X1,esk5_0)|r2_hidden(esk2_3(esk3_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_10]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0),esk1_3(esk3_0,k4_waybel_0(esk3_0,esk4_0),esk5_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_20]), c_0_11]), c_0_42])]), c_0_43]), ['final']).
% 0.21/0.38  cnf(c_0_57, negated_conjecture, (r1_lattice3(esk3_0,k4_waybel_0(esk3_0,esk4_0),X1)|r1_lattice3(esk3_0,esk4_0,esk5_0)|~r1_orders_2(esk3_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_44]), c_0_23]), c_0_10]), c_0_11])]), ['final']).
% 0.21/0.38  cnf(c_0_58, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.21/0.38  cnf(c_0_59, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.38  cnf(c_0_60, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_10]), c_0_11]), c_0_42])]), c_0_43]), ['final']).
% 0.21/0.38  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.21/0.38  # SZS output end Saturation
% 0.21/0.38  # Proof object total steps             : 62
% 0.21/0.38  # Proof object clause steps            : 51
% 0.21/0.38  # Proof object formula steps           : 11
% 0.21/0.38  # Proof object conjectures             : 43
% 0.21/0.38  # Proof object clause conjectures      : 40
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 19
% 0.21/0.38  # Proof object initial formulas used   : 5
% 0.21/0.38  # Proof object generating inferences   : 32
% 0.21/0.38  # Proof object simplifying inferences  : 68
% 0.21/0.38  # Parsed axioms                        : 5
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 19
% 0.21/0.38  # Removed in clause preprocessing      : 0
% 0.21/0.38  # Initial clauses in saturation        : 19
% 0.21/0.38  # Processed clauses                    : 86
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 16
% 0.21/0.38  # ...remaining for further processing  : 70
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 0
% 0.21/0.38  # Generated clauses                    : 53
% 0.21/0.38  # ...of the previous two non-trivial   : 48
% 0.21/0.38  # Contextual simplify-reflections      : 5
% 0.21/0.38  # Paramodulations                      : 51
% 0.21/0.38  # Factorizations                       : 2
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
% 0.21/0.38  # Current number of processed clauses  : 51
% 0.21/0.38  #    Positive orientable unit clauses  : 6
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 44
% 0.21/0.38  # Current number of unprocessed clauses: 0
% 0.21/0.38  # ...number of literals in the above   : 0
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 19
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 1165
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 173
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 21
% 0.21/0.38  # Unit Clause-clause subsumption calls : 1
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 0
% 0.21/0.38  # BW rewrite match successes           : 0
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 4231
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.032 s
% 0.21/0.38  # System time              : 0.005 s
% 0.21/0.38  # Total time               : 0.036 s
% 0.21/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
