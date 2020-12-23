%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1534+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:21 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   28 ( 100 expanded)
%              Number of clauses        :   21 (  34 expanded)
%              Number of leaves         :    3 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 591 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_yellow_0,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,X2,X3)
                  & r1_orders_2(X1,X4,X3) )
               => r1_lattice3(X1,X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_0)).

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

fof(t26_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( ( r1_lattice3(X1,X2,X3)
                    & r1_orders_2(X1,X4,X3) )
                 => r1_lattice3(X1,X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_yellow_0])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_hidden(X8,X6)
        | r1_orders_2(X5,X7,X8)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X7,esk1_3(X5,X6,X7))
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_5,negated_conjecture,
    ( v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & r1_lattice3(esk2_0,esk3_0,esk4_0)
    & r1_orders_2(esk2_0,esk5_0,esk4_0)
    & ~ r1_lattice3(esk2_0,esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk5_0)
    | m1_subset_1(esk1_3(esk2_0,X1,esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,X2,esk5_0))
    | r1_lattice3(esk2_0,X2,esk5_0)
    | ~ r2_hidden(esk1_3(esk2_0,X2,esk5_0),X3)
    | ~ r1_lattice3(esk2_0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_8])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,X1,esk5_0),X1)
    | r1_lattice3(esk2_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_7]),c_0_8])])).

fof(c_0_14,plain,(
    ! [X10,X11,X12,X13] :
      ( ~ v4_orders_2(X10)
      | ~ l1_orders_2(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ m1_subset_1(X13,u1_struct_0(X10))
      | ~ r1_orders_2(X10,X11,X12)
      | ~ r1_orders_2(X10,X12,X13)
      | r1_orders_2(X10,X11,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,X2,esk5_0))
    | r1_lattice3(esk2_0,X2,esk5_0)
    | ~ r1_lattice3(esk2_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk1_3(esk2_0,X1,esk5_0))
    | r1_lattice3(esk2_0,X1,esk5_0)
    | ~ r1_lattice3(esk2_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_lattice3(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,X2,esk5_0))
    | r1_lattice3(esk2_0,X2,esk5_0)
    | ~ r1_orders_2(esk2_0,X3,esk1_3(esk2_0,X2,esk5_0))
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_18]),c_0_8])])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk1_3(esk2_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_24,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk5_0))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_16])]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_7]),c_0_8]),c_0_26])]),c_0_21]),
    [proof]).

%------------------------------------------------------------------------------
