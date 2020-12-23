%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1568+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:24 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  119 (927502 expanded)
%              Number of clauses        :  114 (372843 expanded)
%              Number of leaves         :    2 (205064 expanded)
%              Depth                    :   46
%              Number of atoms          :  564 (11497823 expanded)
%              Number of equality atoms :   74 (437443 expanded)
%              Maximal formula depth    :   33 (   5 average)
%              Maximal clause size      :  107 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                <=> r2_lattice3(X1,X3,X4) ) )
            & r1_yellow_0(X1,X2) )
         => r1_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_0)).

fof(d7_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) )
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r2_lattice3(X1,X2,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r2_lattice3(X1,X2,X5)
                           => r1_orders_2(X1,X4,X5) ) ) )
                   => X4 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_0)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( ( ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                  <=> r2_lattice3(X1,X3,X4) ) )
              & r1_yellow_0(X1,X2) )
           => r1_yellow_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t46_yellow_0])).

fof(c_0_3,plain,(
    ! [X6,X7,X9,X10,X12,X13,X16] :
      ( ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X7,esk1_2(X6,X7))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X7,X9)
        | r1_orders_2(X6,esk1_2(X6,X7),X9)
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X10),u1_struct_0(X6))
        | ~ r2_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X7,esk2_3(X6,X7,X10))
        | ~ r2_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( ~ r1_orders_2(X6,X10,esk2_3(X6,X7,X10))
        | ~ r2_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X16)
        | r1_orders_2(X6,esk4_3(X6,X12,X13),X16)
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X16)
        | r1_orders_2(X6,esk4_3(X6,X12,X13),X16)
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X16)
        | r1_orders_2(X6,esk4_3(X6,X12,X13),X16)
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_yellow_0])])])])])])).

fof(c_0_4,negated_conjecture,(
    ! [X20] :
      ( ~ v2_struct_0(esk5_0)
      & l1_orders_2(esk5_0)
      & ( ~ r2_lattice3(esk5_0,esk6_0,X20)
        | r2_lattice3(esk5_0,esk7_0,X20)
        | ~ m1_subset_1(X20,u1_struct_0(esk5_0)) )
      & ( ~ r2_lattice3(esk5_0,esk7_0,X20)
        | r2_lattice3(esk5_0,esk6_0,X20)
        | ~ m1_subset_1(X20,u1_struct_0(esk5_0)) )
      & r1_yellow_0(esk5_0,esk6_0)
      & ~ r1_yellow_0(esk5_0,esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).

cnf(c_0_5,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_8,negated_conjecture,
    ( r1_yellow_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,X1)
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk1_2(esk5_0,X1))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_6])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))
    | ~ r2_lattice3(esk5_0,esk6_0,esk1_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk1_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_8])).

cnf(c_0_16,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_17,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_6])])).

cnf(c_0_18,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_yellow_0(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_22,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_11]),c_0_6])])).

cnf(c_0_23,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,X1)
    | ~ r2_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,X1,esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_11]),c_0_6])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_11]),c_0_6])])).

cnf(c_0_27,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = esk1_2(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | X3 = esk1_2(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_37,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | m1_subset_1(esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_6])])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | r2_lattice3(esk5_0,X1,esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_6])])).

cnf(c_0_40,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_6])])).

cnf(c_0_41,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_38]),c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_8])).

cnf(c_0_44,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_8]),c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | r2_lattice3(esk5_0,X1,esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_6])])).

cnf(c_0_46,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | m1_subset_1(esk3_3(X2,X3,X4),u1_struct_0(X2))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_47,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_8]),c_0_32])).

cnf(c_0_51,plain,
    ( X2 = esk1_2(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk5_0,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),X2)
    | m1_subset_1(esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0))
    | ~ r2_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_11]),c_0_6])])).

cnf(c_0_53,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_47]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | r2_lattice3(X2,X3,esk3_3(X2,X3,X4))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_56,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | ~ r1_orders_2(esk5_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_30]),c_0_6])])).

cnf(c_0_57,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,X1,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_53]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk5_0,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),X2)
    | r2_lattice3(esk5_0,X1,esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0))
    | ~ r2_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_11]),c_0_6])])).

cnf(c_0_60,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_orders_2(esk5_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_24]),c_0_6])])).

cnf(c_0_61,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_62,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | ~ r1_orders_2(esk5_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_8])).

cnf(c_0_63,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_18]),c_0_19]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,X1,esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,X1,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_44])).

cnf(c_0_65,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_orders_2(esk5_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_8]),c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_2(esk5_0,X1),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,X1,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_27]),c_0_6])])).

cnf(c_0_67,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_42])).

cnf(c_0_68,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_18]),c_0_19]),c_0_54]),c_0_65])).

cnf(c_0_69,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_70,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_8])).

cnf(c_0_71,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_67]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | r1_yellow_0(esk5_0,X1)
    | ~ r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_11]),c_0_6])])).

cnf(c_0_73,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_18])]),c_0_19])).

cnf(c_0_75,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_74])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_77,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk1_2(esk5_0,X1),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,X1,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_75]),c_0_6])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | r1_yellow_0(esk5_0,X1)
    | ~ r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_11]),c_0_6])])).

cnf(c_0_79,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_8]),c_0_42])).

cnf(c_0_80,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | m1_subset_1(esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_18])]),c_0_19])).

cnf(c_0_81,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_80]),c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_82]),c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk1_2(esk5_0,X1),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_84]),c_0_6])])).

cnf(c_0_86,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk1_2(esk5_0,X1),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_83]),c_0_6])])).

cnf(c_0_87,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_8]),c_0_71])).

cnf(c_0_88,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_8]),c_0_71])).

cnf(c_0_89,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_87]),c_0_18])]),c_0_19])).

cnf(c_0_90,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_88]),c_0_18])]),c_0_19])).

cnf(c_0_91,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_89]),c_0_6])])).

cnf(c_0_92,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r2_lattice3(esk5_0,X1,esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_90]),c_0_6])])).

cnf(c_0_93,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_8]),c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk6_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_8]),c_0_81])).

cnf(c_0_95,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | m1_subset_1(esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,X1,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_82])).

cnf(c_0_96,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r2_lattice3(esk5_0,esk7_0,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_93]),c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_18]),c_0_19]),c_0_96])).

cnf(c_0_98,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_97]),c_0_81])).

cnf(c_0_99,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk1_2(esk5_0,X1),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,X1,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_98]),c_0_6])])).

cnf(c_0_100,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_8]),c_0_71])).

cnf(c_0_101,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | m1_subset_1(esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_100]),c_0_18])]),c_0_19])).

cnf(c_0_102,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,esk3_3(X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_103,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | m1_subset_1(esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_101]),c_0_6])])).

cnf(c_0_104,negated_conjecture,
    ( r1_orders_2(esk5_0,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),X2)
    | r1_yellow_0(esk5_0,X1)
    | ~ r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0))
    | ~ r2_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_11]),c_0_6])])).

cnf(c_0_105,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_8]),c_0_81])).

cnf(c_0_106,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,X1)
    | ~ r1_orders_2(esk5_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_101]),c_0_6])])).

cnf(c_0_107,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | r1_orders_2(esk5_0,esk4_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | r1_yellow_0(esk5_0,X1)
    | ~ r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,X1,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,X1,esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))))
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | ~ r1_orders_2(esk5_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),esk2_3(esk5_0,esk6_0,esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_8]),c_0_81])).

cnf(c_0_109,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_110,negated_conjecture,
    ( esk4_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_100]),c_0_18])]),c_0_19]),c_0_96]),c_0_108])).

cnf(c_0_111,plain,
    ( r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_18]),c_0_11]),c_0_6])]),c_0_19])).

cnf(c_0_113,negated_conjecture,
    ( r2_lattice3(esk5_0,esk7_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_110]),c_0_18]),c_0_11]),c_0_6])]),c_0_19])).

cnf(c_0_114,plain,
    ( r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_115,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_2(esk5_0,X1),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r2_lattice3(esk5_0,X1,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0)))
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_112]),c_0_6])])).

cnf(c_0_116,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_112]),c_0_113])])).

cnf(c_0_117,negated_conjecture,
    ( ~ r1_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk3_3(esk5_0,esk7_0,esk1_2(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_110]),c_0_18]),c_0_11]),c_0_6])]),c_0_19])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_8]),c_0_116])]),c_0_117]),
    [proof]).

%------------------------------------------------------------------------------
