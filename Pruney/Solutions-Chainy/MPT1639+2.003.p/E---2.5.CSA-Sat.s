%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:10 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 425 expanded)
%              Number of clauses        :   55 ( 157 expanded)
%              Number of leaves         :    4 ( 109 expanded)
%              Depth                    :    7
%              Number of atoms          :  398 (3999 expanded)
%              Number of equality atoms :   29 ( 462 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t19_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k5_waybel_0(X1,X2) = k5_waybel_0(X1,X3)
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_0)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(c_0_4,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_hidden(X10,X8)
        | r1_orders_2(X7,X10,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))
        | r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,esk1_3(X7,X8,X9),X9)
        | r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_5,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_6,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k5_waybel_0(X1,X2) = k5_waybel_0(X1,X3)
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_waybel_0])).

cnf(c_0_8,plain,
    ( r2_lattice3(X1,X2,X3)
    | r1_orders_2(X1,esk1_3(X1,X2,X3),X4)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X5)
    | ~ r2_lattice3(X1,X5,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6]),
    [final]).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( r2_lattice3(X12,X14,X13)
        | X13 != k1_yellow_0(X12,X14)
        | ~ r1_yellow_0(X12,X14)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_lattice3(X12,X14,X15)
        | r1_orders_2(X12,X13,X15)
        | X13 != k1_yellow_0(X12,X14)
        | ~ r1_yellow_0(X12,X14)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( X13 = k1_yellow_0(X12,X16)
        | m1_subset_1(esk2_3(X12,X13,X16),u1_struct_0(X12))
        | ~ r2_lattice3(X12,X16,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r1_yellow_0(X12,X16)
        | m1_subset_1(esk2_3(X12,X13,X16),u1_struct_0(X12))
        | ~ r2_lattice3(X12,X16,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( X13 = k1_yellow_0(X12,X16)
        | r2_lattice3(X12,X16,esk2_3(X12,X13,X16))
        | ~ r2_lattice3(X12,X16,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r1_yellow_0(X12,X16)
        | r2_lattice3(X12,X16,esk2_3(X12,X13,X16))
        | ~ r2_lattice3(X12,X16,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( X13 = k1_yellow_0(X12,X16)
        | ~ r1_orders_2(X12,X13,esk2_3(X12,X13,X16))
        | ~ r2_lattice3(X12,X16,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r1_yellow_0(X12,X16)
        | ~ r1_orders_2(X12,X13,esk2_3(X12,X13,X16))
        | ~ r2_lattice3(X12,X16,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & k5_waybel_0(esk3_0,esk4_0) = k5_waybel_0(esk3_0,esk5_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_12,plain,
    ( r2_lattice3(X1,X2,X3)
    | r1_orders_2(X1,esk1_3(X1,X2,X3),X4)
    | ~ r2_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9]),
    [final]).

cnf(c_0_13,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,plain,
    ( r1_yellow_0(X1,X2)
    | m1_subset_1(esk2_3(X1,X3,X2),u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_18,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_19,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X4,X5)
    | r1_orders_2(X2,esk1_3(X2,X4,X5),esk2_3(X2,X1,X3))
    | ~ v5_orders_2(X2)
    | ~ r2_lattice3(X2,X4,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_20,plain,
    ( r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_21,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X3,X4)
    | r1_orders_2(X1,esk1_3(X1,X3,X4),esk2_3(X1,X5,X2))
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X3,esk2_3(X1,X5,X2))
    | ~ r2_lattice3(X1,X2,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,X1)
    | ~ r2_hidden(esk4_0,X2)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_15]),c_0_16])]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_24,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ v3_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | r1_orders_2(X5,X6,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,X1)
    | ~ r2_hidden(esk5_0,X2)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_17]),c_0_16])]),
    [final]).

cnf(c_0_26,plain,
    ( esk1_3(X1,X2,X3) = k1_yellow_0(X1,X4)
    | r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,esk2_3(X1,esk1_3(X1,X2,X3),X4))
    | ~ r2_lattice3(X1,X4,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_6]),
    [final]).

cnf(c_0_27,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk2_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_28,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X3,X4)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X3,esk2_3(X1,esk1_3(X1,X3,X4),X2))
    | ~ r2_lattice3(X1,X2,esk1_3(X1,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_6]),
    [final]).

cnf(c_0_29,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( X1 = k1_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X1,X2))
    | ~ r2_hidden(esk4_0,X3)
    | ~ r2_lattice3(esk3_0,X3,esk2_3(esk3_0,X1,X2))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_13]),c_0_23]),c_0_16])]),
    [final]).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( X1 = k1_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X1,X2))
    | ~ r2_hidden(esk5_0,X3)
    | ~ r2_lattice3(esk3_0,X3,esk2_3(esk3_0,X1,X2))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_13]),c_0_23]),c_0_16])]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( r1_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X2,X1))
    | ~ r2_hidden(esk4_0,X3)
    | ~ r2_lattice3(esk3_0,X3,esk2_3(esk3_0,X2,X1))
    | ~ r2_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_14]),c_0_23]),c_0_16])]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( r1_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X2,X1))
    | ~ r2_hidden(esk5_0,X3)
    | ~ r2_lattice3(esk3_0,X3,esk2_3(esk3_0,X2,X1))
    | ~ r2_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_23]),c_0_16])]),
    [final]).

cnf(c_0_35,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_39,plain,
    ( esk1_3(X1,X2,X3) = k1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_6]),
    [final]).

cnf(c_0_40,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_6]),
    [final]).

cnf(c_0_41,plain,
    ( r2_lattice3(X1,X2,X3)
    | r2_lattice3(X1,X4,X5)
    | r1_orders_2(X1,esk1_3(X1,X4,X5),esk1_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X4,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_6]),
    [final]).

cnf(c_0_42,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r1_orders_2(X2,esk2_3(X2,X1,X3),X4)
    | ~ v5_orders_2(X2)
    | ~ r2_hidden(esk2_3(X2,X1,X3),X5)
    | ~ r2_lattice3(X2,X5,X4)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_5,c_0_13]),
    [final]).

cnf(c_0_43,plain,
    ( r1_yellow_0(X1,X2)
    | r1_orders_2(X1,esk2_3(X1,X3,X2),X4)
    | ~ v5_orders_2(X1)
    | ~ r2_hidden(esk2_3(X1,X3,X2),X5)
    | ~ r2_lattice3(X1,X5,X4)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_14]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk4_0)
    | ~ r2_lattice3(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_15]),c_0_16])]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk5_0)
    | ~ r2_lattice3(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_17]),c_0_16])]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( X1 = k1_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X1,X2))
    | ~ r2_hidden(esk4_0,X2)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_23]),c_0_16])]),
    [final]).

cnf(c_0_47,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r1_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_13]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( X1 = k1_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X1,X2))
    | ~ r2_hidden(esk5_0,X2)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_23]),c_0_16])]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r1_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X2,X1))
    | ~ r2_hidden(esk4_0,X1)
    | ~ r2_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_23]),c_0_16])]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( r1_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X2,X1))
    | ~ r2_hidden(esk5_0,X1)
    | ~ r2_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_23]),c_0_16])]),
    [final]).

cnf(c_0_51,plain,
    ( r1_yellow_0(X1,X2)
    | r1_orders_2(X1,esk2_3(X1,X3,X2),esk2_3(X1,X3,X2))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_14]),
    [final]).

cnf(c_0_52,plain,
    ( r2_lattice3(X1,X2,X3)
    | r1_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_6]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,X1,X2))
    | ~ r2_hidden(esk4_0,X3)
    | ~ r2_lattice3(esk3_0,X3,esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_6]),c_0_16])]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,X1,X2))
    | ~ r2_hidden(esk5_0,X3)
    | ~ r2_lattice3(esk3_0,X3,esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_6]),c_0_16])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ r2_lattice3(esk3_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_15]),
    [final]).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_58,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_59,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_15]),c_0_16]),c_0_37])]),c_0_38]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_17]),c_0_16]),c_0_37])]),c_0_38]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k5_waybel_0(esk3_0,esk4_0) = k5_waybel_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.38  fof(t19_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k5_waybel_0(X1,X2)=k5_waybel_0(X1,X3)=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_waybel_0)).
% 0.13/0.38  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.13/0.38  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.13/0.38  fof(c_0_4, plain, ![X7, X8, X9, X10]:((~r2_lattice3(X7,X8,X9)|(~m1_subset_1(X10,u1_struct_0(X7))|(~r2_hidden(X10,X8)|r1_orders_2(X7,X10,X9)))|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&((m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))|r2_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&((r2_hidden(esk1_3(X7,X8,X9),X8)|r2_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&(~r1_orders_2(X7,esk1_3(X7,X8,X9),X9)|r2_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.38  cnf(c_0_5, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_6, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k5_waybel_0(X1,X2)=k5_waybel_0(X1,X3)=>X2=X3))))), inference(assume_negation,[status(cth)],[t19_waybel_0])).
% 0.13/0.38  cnf(c_0_8, plain, (r2_lattice3(X1,X2,X3)|r1_orders_2(X1,esk1_3(X1,X2,X3),X4)|~r2_hidden(esk1_3(X1,X2,X3),X5)|~r2_lattice3(X1,X5,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_5, c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_9, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  fof(c_0_10, plain, ![X12, X13, X14, X15, X16]:(((r2_lattice3(X12,X14,X13)|(X13!=k1_yellow_0(X12,X14)|~r1_yellow_0(X12,X14))|~m1_subset_1(X13,u1_struct_0(X12))|(~v5_orders_2(X12)|~l1_orders_2(X12)))&(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_lattice3(X12,X14,X15)|r1_orders_2(X12,X13,X15))|(X13!=k1_yellow_0(X12,X14)|~r1_yellow_0(X12,X14))|~m1_subset_1(X13,u1_struct_0(X12))|(~v5_orders_2(X12)|~l1_orders_2(X12))))&(((X13=k1_yellow_0(X12,X16)|(m1_subset_1(esk2_3(X12,X13,X16),u1_struct_0(X12))|~r2_lattice3(X12,X16,X13))|~m1_subset_1(X13,u1_struct_0(X12))|(~v5_orders_2(X12)|~l1_orders_2(X12)))&(r1_yellow_0(X12,X16)|(m1_subset_1(esk2_3(X12,X13,X16),u1_struct_0(X12))|~r2_lattice3(X12,X16,X13))|~m1_subset_1(X13,u1_struct_0(X12))|(~v5_orders_2(X12)|~l1_orders_2(X12))))&(((X13=k1_yellow_0(X12,X16)|(r2_lattice3(X12,X16,esk2_3(X12,X13,X16))|~r2_lattice3(X12,X16,X13))|~m1_subset_1(X13,u1_struct_0(X12))|(~v5_orders_2(X12)|~l1_orders_2(X12)))&(r1_yellow_0(X12,X16)|(r2_lattice3(X12,X16,esk2_3(X12,X13,X16))|~r2_lattice3(X12,X16,X13))|~m1_subset_1(X13,u1_struct_0(X12))|(~v5_orders_2(X12)|~l1_orders_2(X12))))&((X13=k1_yellow_0(X12,X16)|(~r1_orders_2(X12,X13,esk2_3(X12,X13,X16))|~r2_lattice3(X12,X16,X13))|~m1_subset_1(X13,u1_struct_0(X12))|(~v5_orders_2(X12)|~l1_orders_2(X12)))&(r1_yellow_0(X12,X16)|(~r1_orders_2(X12,X13,esk2_3(X12,X13,X16))|~r2_lattice3(X12,X16,X13))|~m1_subset_1(X13,u1_struct_0(X12))|(~v5_orders_2(X12)|~l1_orders_2(X12))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(k5_waybel_0(esk3_0,esk4_0)=k5_waybel_0(esk3_0,esk5_0)&esk4_0!=esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.13/0.38  cnf(c_0_12, plain, (r2_lattice3(X1,X2,X3)|r1_orders_2(X1,esk1_3(X1,X2,X3),X4)|~r2_lattice3(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_8, c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_13, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_14, plain, (r1_yellow_0(X1,X2)|m1_subset_1(esk2_3(X1,X3,X2),u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_18, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_19, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X4,X5)|r1_orders_2(X2,esk1_3(X2,X4,X5),esk2_3(X2,X1,X3))|~v5_orders_2(X2)|~r2_lattice3(X2,X4,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_20, plain, (r1_yellow_0(X1,X2)|~r1_orders_2(X1,X3,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_21, plain, (r1_yellow_0(X1,X2)|r2_lattice3(X1,X3,X4)|r1_orders_2(X1,esk1_3(X1,X3,X4),esk2_3(X1,X5,X2))|~v5_orders_2(X1)|~r2_lattice3(X1,X3,esk2_3(X1,X5,X2))|~r2_lattice3(X1,X2,X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_12, c_0_14]), ['final']).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,X1)|~r2_hidden(esk4_0,X2)|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_15]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.38  fof(c_0_24, plain, ![X5, X6]:(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|r1_orders_2(X5,X6,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,X1)|~r2_hidden(esk5_0,X2)|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_17]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_26, plain, (esk1_3(X1,X2,X3)=k1_yellow_0(X1,X4)|r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~r2_lattice3(X1,X2,esk2_3(X1,esk1_3(X1,X2,X3),X4))|~r2_lattice3(X1,X4,esk1_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_27, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X3,esk2_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_28, plain, (r1_yellow_0(X1,X2)|r2_lattice3(X1,X3,X4)|~v5_orders_2(X1)|~r2_lattice3(X1,X3,esk2_3(X1,esk1_3(X1,X3,X4),X2))|~r2_lattice3(X1,X2,esk1_3(X1,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_29, plain, (r1_yellow_0(X1,X2)|r2_lattice3(X1,X2,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (X1=k1_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X1,X2))|~r2_hidden(esk4_0,X3)|~r2_lattice3(esk3_0,X3,esk2_3(esk3_0,X1,X2))|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_13]), c_0_23]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_31, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (X1=k1_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X1,X2))|~r2_hidden(esk5_0,X3)|~r2_lattice3(esk3_0,X3,esk2_3(esk3_0,X1,X2))|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_13]), c_0_23]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r1_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X2,X1))|~r2_hidden(esk4_0,X3)|~r2_lattice3(esk3_0,X3,esk2_3(esk3_0,X2,X1))|~r2_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_14]), c_0_23]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (r1_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X2,X1))|~r2_hidden(esk5_0,X3)|~r2_lattice3(esk3_0,X3,esk2_3(esk3_0,X2,X1))|~r2_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_14]), c_0_23]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_35, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_36, plain, (r2_lattice3(X1,X2,X3)|X3!=k1_yellow_0(X1,X2)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_39, plain, (esk1_3(X1,X2,X3)=k1_yellow_0(X1,X2)|r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~r2_lattice3(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_40, plain, (r1_yellow_0(X1,X2)|r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~r2_lattice3(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_41, plain, (r2_lattice3(X1,X2,X3)|r2_lattice3(X1,X4,X5)|r1_orders_2(X1,esk1_3(X1,X4,X5),esk1_3(X1,X2,X3))|~r2_lattice3(X1,X4,esk1_3(X1,X2,X3))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_12, c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_42, plain, (X1=k1_yellow_0(X2,X3)|r1_orders_2(X2,esk2_3(X2,X1,X3),X4)|~v5_orders_2(X2)|~r2_hidden(esk2_3(X2,X1,X3),X5)|~r2_lattice3(X2,X5,X4)|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_5, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_43, plain, (r1_yellow_0(X1,X2)|r1_orders_2(X1,esk2_3(X1,X3,X2),X4)|~v5_orders_2(X1)|~r2_hidden(esk2_3(X1,X3,X2),X5)|~r2_lattice3(X1,X5,X4)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_5, c_0_14]), ['final']).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk4_0)|~r2_lattice3(esk3_0,X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_15]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk5_0)|~r2_lattice3(esk3_0,X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_17]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (X1=k1_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X1,X2))|~r2_hidden(esk4_0,X2)|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_23]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_47, plain, (X1=k1_yellow_0(X2,X3)|r1_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X1,X3))|v2_struct_0(X2)|~v5_orders_2(X2)|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_31, c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (X1=k1_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X1,X2))|~r2_hidden(esk5_0,X2)|~r2_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_23]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (r1_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X2,X1))|~r2_hidden(esk4_0,X1)|~r2_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_23]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r1_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X2,X1))|~r2_hidden(esk5_0,X1)|~r2_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_29]), c_0_23]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_51, plain, (r1_yellow_0(X1,X2)|r1_orders_2(X1,esk2_3(X1,X3,X2),esk2_3(X1,X3,X2))|v2_struct_0(X1)|~v5_orders_2(X1)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_31, c_0_14]), ['final']).
% 0.13/0.38  cnf(c_0_52, plain, (r2_lattice3(X1,X2,X3)|r1_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_31, c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,X1,X2))|~r2_hidden(esk4_0,X3)|~r2_lattice3(esk3_0,X3,esk1_3(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_6]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (r2_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,X1,X2))|~r2_hidden(esk5_0,X3)|~r2_lattice3(esk3_0,X3,esk1_3(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_6]), c_0_16])]), ['final']).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk5_0)|~r2_hidden(esk4_0,X1)|~r2_lattice3(esk3_0,X1,esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk4_0)|~r2_hidden(esk5_0,X1)|~r2_lattice3(esk3_0,X1,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_57, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_35]), ['final']).
% 0.13/0.38  cnf(c_0_58, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_36]), ['final']).
% 0.13/0.38  cnf(c_0_59, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_15]), c_0_16]), c_0_37])]), c_0_38]), ['final']).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_17]), c_0_16]), c_0_37])]), c_0_38]), ['final']).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k5_waybel_0(esk3_0,esk4_0)=k5_waybel_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 64
% 0.13/0.38  # Proof object clause steps            : 55
% 0.13/0.38  # Proof object formula steps           : 9
% 0.13/0.38  # Proof object conjectures             : 29
% 0.13/0.38  # Proof object clause conjectures      : 26
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 21
% 0.13/0.38  # Proof object initial formulas used   : 4
% 0.13/0.38  # Proof object generating inferences   : 32
% 0.13/0.38  # Proof object simplifying inferences  : 50
% 0.13/0.38  # Parsed axioms                        : 4
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 21
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 21
% 0.13/0.38  # Processed clauses                    : 84
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 8
% 0.13/0.38  # ...remaining for further processing  : 76
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 49
% 0.13/0.38  # ...of the previous two non-trivial   : 42
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 47
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 53
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 43
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 21
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 865
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 98
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3843
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.036 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
