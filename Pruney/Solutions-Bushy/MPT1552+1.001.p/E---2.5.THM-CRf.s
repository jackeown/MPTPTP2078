%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1552+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:23 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 419 expanded)
%              Number of clauses        :   29 ( 134 expanded)
%              Number of leaves         :    3 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  272 (8169 expanded)
%              Number of equality atoms :   35 (1063 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   57 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_yellow_0,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(t15_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t30_yellow_0])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8] :
      ( ( r2_lattice3(X5,X6,X7)
        | X7 != k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_lattice3(X5,X6,X8)
        | r1_orders_2(X5,X7,X8)
        | X7 != k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | ~ r2_lattice3(X5,X6,X7)
        | X7 = k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( r2_lattice3(X5,X6,esk1_3(X5,X6,X7))
        | ~ r2_lattice3(X5,X6,X7)
        | X7 = k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X7,esk1_3(X5,X6,X7))
        | ~ r2_lattice3(X5,X6,X7)
        | X7 = k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X21] :
      ( v5_orders_2(esk4_0)
      & l1_orders_2(esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
      & ( r2_lattice3(esk4_0,esk6_0,esk5_0)
        | esk5_0 = k1_yellow_0(esk4_0,esk6_0) )
      & ( ~ m1_subset_1(X21,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,X21)
        | r1_orders_2(esk4_0,esk5_0,X21)
        | esk5_0 = k1_yellow_0(esk4_0,esk6_0) )
      & ( esk5_0 != k1_yellow_0(esk4_0,esk6_0)
        | ~ r1_yellow_0(esk4_0,esk6_0)
        | esk5_0 = k1_yellow_0(esk4_0,esk6_0) )
      & ( r2_lattice3(esk4_0,esk6_0,esk5_0)
        | r1_yellow_0(esk4_0,esk6_0) )
      & ( ~ m1_subset_1(X21,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,X21)
        | r1_orders_2(esk4_0,esk5_0,X21)
        | r1_yellow_0(esk4_0,esk6_0) )
      & ( esk5_0 != k1_yellow_0(esk4_0,esk6_0)
        | ~ r1_yellow_0(esk4_0,esk6_0)
        | r1_yellow_0(esk4_0,esk6_0) )
      & ( r2_lattice3(esk4_0,esk6_0,esk5_0)
        | m1_subset_1(esk7_0,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) )
      & ( ~ m1_subset_1(X21,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,X21)
        | r1_orders_2(esk4_0,esk5_0,X21)
        | m1_subset_1(esk7_0,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) )
      & ( esk5_0 != k1_yellow_0(esk4_0,esk6_0)
        | ~ r1_yellow_0(esk4_0,esk6_0)
        | m1_subset_1(esk7_0,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) )
      & ( r2_lattice3(esk4_0,esk6_0,esk5_0)
        | r2_lattice3(esk4_0,esk6_0,esk7_0)
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) )
      & ( ~ m1_subset_1(X21,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,X21)
        | r1_orders_2(esk4_0,esk5_0,X21)
        | r2_lattice3(esk4_0,esk6_0,esk7_0)
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) )
      & ( esk5_0 != k1_yellow_0(esk4_0,esk6_0)
        | ~ r1_yellow_0(esk4_0,esk6_0)
        | r2_lattice3(esk4_0,esk6_0,esk7_0)
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) )
      & ( r2_lattice3(esk4_0,esk6_0,esk5_0)
        | ~ r1_orders_2(esk4_0,esk5_0,esk7_0)
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) )
      & ( ~ m1_subset_1(X21,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,X21)
        | r1_orders_2(esk4_0,esk5_0,X21)
        | ~ r1_orders_2(esk4_0,esk5_0,esk7_0)
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) )
      & ( esk5_0 != k1_yellow_0(esk4_0,esk6_0)
        | ~ r1_yellow_0(esk4_0,esk6_0)
        | ~ r1_orders_2(esk4_0,esk5_0,esk7_0)
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( m1_subset_1(esk2_2(X10,X11),u1_struct_0(X10))
        | ~ r1_yellow_0(X10,X11)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,X11,esk2_2(X10,X11))
        | ~ r1_yellow_0(X10,X11)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X11,X13)
        | r1_orders_2(X10,esk2_2(X10,X11),X13)
        | ~ r1_yellow_0(X10,X11)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk3_3(X10,X14,X15),u1_struct_0(X10))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X14,X15)
        | r1_yellow_0(X10,X14)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,X14,esk3_3(X10,X14,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X14,X15)
        | r1_yellow_0(X10,X14)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,X15,esk3_3(X10,X14,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X14,X15)
        | r1_yellow_0(X10,X14)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

cnf(c_0_7,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk3_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | r1_yellow_0(esk4_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | esk5_0 != k1_yellow_0(esk4_0,esk6_0)
    | ~ r1_yellow_0(esk4_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    | esk5_0 != k1_yellow_0(esk4_0,esk6_0)
    | ~ r1_yellow_0(esk4_0,esk6_0)
    | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | esk5_0 != k1_yellow_0(esk4_0,X1)
    | ~ r1_yellow_0(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_17,negated_conjecture,
    ( r1_yellow_0(esk4_0,esk6_0)
    | r1_yellow_0(esk4_0,X1)
    | ~ r2_lattice3(esk4_0,esk6_0,esk3_3(esk4_0,X1,esk5_0))
    | ~ r2_lattice3(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(esk3_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_8]),c_0_9])])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( esk5_0 != k1_yellow_0(esk4_0,esk6_0)
    | ~ r1_yellow_0(esk4_0,esk6_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk7_0)
    | ~ r2_lattice3(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk7_0)
    | esk5_0 != k1_yellow_0(esk4_0,esk6_0)
    | X1 != k1_yellow_0(esk4_0,esk6_0)
    | ~ r1_yellow_0(esk4_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_9])]),c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_yellow_0(esk4_0,esk6_0)
    | r1_yellow_0(esk4_0,X1)
    | ~ r2_lattice3(esk4_0,esk6_0,esk3_3(esk4_0,X1,esk5_0))
    | ~ r2_lattice3(esk4_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_12]),c_0_8]),c_0_9])])).

cnf(c_0_22,plain,
    ( r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk5_0)
    | r1_yellow_0(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 != k1_yellow_0(esk4_0,esk6_0)
    | ~ r1_yellow_0(esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_8])]),c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( r1_yellow_0(esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_12]),c_0_8]),c_0_9])]),c_0_23])).

cnf(c_0_26,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | esk5_0 = k1_yellow_0(esk4_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_28,negated_conjecture,
    ( esk5_0 != k1_yellow_0(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,X1)
    | ~ r2_lattice3(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk5_0))
    | ~ r2_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_yellow_0(esk4_0,X1)
    | ~ m1_subset_1(esk1_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_8]),c_0_9])]),c_0_28])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk5_0)
    | esk5_0 = k1_yellow_0(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,X1)
    | ~ r2_lattice3(esk4_0,esk6_0,esk1_3(esk4_0,X1,esk5_0))
    | ~ r2_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_yellow_0(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_8]),c_0_9])])).

cnf(c_0_33,plain,
    ( r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_25]),c_0_8]),c_0_9])]),c_0_28]),
    [proof]).

%------------------------------------------------------------------------------
