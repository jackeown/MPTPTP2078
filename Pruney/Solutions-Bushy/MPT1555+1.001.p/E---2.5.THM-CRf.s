%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1555+1.001 : TPTP v7.4.0. Released v7.4.0.
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
% Statistics : Number of formulae       :   34 ( 655 expanded)
%              Number of clauses        :   27 ( 212 expanded)
%              Number of leaves         :    3 ( 158 expanded)
%              Depth                    :   12
%              Number of atoms          :  200 (6833 expanded)
%              Number of equality atoms :   32 (1076 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k2_yellow_0(X1,X3)
            <=> ( r1_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X3,X4)
                     => r1_orders_2(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_yellow_0)).

fof(t17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).

fof(t31_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) )
               => ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) )
              & ( ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) )
               => ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( X2 = k2_yellow_0(X1,X3)
              <=> ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_yellow_0])).

fof(c_0_4,plain,(
    ! [X5,X6] :
      ( ( r1_yellow_0(X5,X6)
        | v2_struct_0(X5)
        | ~ v5_orders_2(X5)
        | ~ v3_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_yellow_0(X5,X6)
        | v2_struct_0(X5)
        | ~ v5_orders_2(X5)
        | ~ v3_lattice3(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X17] :
      ( ~ v2_struct_0(esk2_0)
      & v5_orders_2(esk2_0)
      & v3_lattice3(esk2_0)
      & l1_orders_2(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & ( m1_subset_1(esk5_0,u1_struct_0(esk2_0))
        | ~ r1_lattice3(esk2_0,esk4_0,esk3_0)
        | esk3_0 != k2_yellow_0(esk2_0,esk4_0) )
      & ( r1_lattice3(esk2_0,esk4_0,esk5_0)
        | ~ r1_lattice3(esk2_0,esk4_0,esk3_0)
        | esk3_0 != k2_yellow_0(esk2_0,esk4_0) )
      & ( ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
        | ~ r1_lattice3(esk2_0,esk4_0,esk3_0)
        | esk3_0 != k2_yellow_0(esk2_0,esk4_0) )
      & ( r1_lattice3(esk2_0,esk4_0,esk3_0)
        | esk3_0 = k2_yellow_0(esk2_0,esk4_0) )
      & ( ~ m1_subset_1(X17,u1_struct_0(esk2_0))
        | ~ r1_lattice3(esk2_0,esk4_0,X17)
        | r1_orders_2(esk2_0,X17,esk3_0)
        | esk3_0 = k2_yellow_0(esk2_0,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( r1_lattice3(X7,X9,X8)
        | X8 != k2_yellow_0(X7,X9)
        | ~ r2_yellow_0(X7,X9)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_lattice3(X7,X9,X10)
        | r1_orders_2(X7,X10,X8)
        | X8 != k2_yellow_0(X7,X9)
        | ~ r2_yellow_0(X7,X9)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( X8 = k2_yellow_0(X7,X11)
        | m1_subset_1(esk1_3(X7,X8,X11),u1_struct_0(X7))
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_yellow_0(X7,X11)
        | m1_subset_1(esk1_3(X7,X8,X11),u1_struct_0(X7))
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( X8 = k2_yellow_0(X7,X11)
        | r1_lattice3(X7,X11,esk1_3(X7,X8,X11))
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_yellow_0(X7,X11)
        | r1_lattice3(X7,X11,esk1_3(X7,X8,X11))
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( X8 = k2_yellow_0(X7,X11)
        | ~ r1_orders_2(X7,esk1_3(X7,X8,X11),X8)
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_yellow_0(X7,X11)
        | ~ r1_orders_2(X7,esk1_3(X7,X8,X11),X8)
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

cnf(c_0_7,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v3_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_yellow_0(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk3_0)
    | esk3_0 != k2_yellow_0(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_8]),c_0_10])]),c_0_14])])).

cnf(c_0_16,negated_conjecture,
    ( r1_lattice3(esk2_0,esk4_0,esk3_0)
    | esk3_0 = k2_yellow_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( r1_lattice3(esk2_0,esk4_0,esk5_0)
    | ~ r1_lattice3(esk2_0,esk4_0,esk3_0)
    | esk3_0 != k2_yellow_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r1_lattice3(esk2_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,esk4_0,esk3_0)
    | esk3_0 != k2_yellow_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
    | ~ r1_lattice3(esk2_0,esk4_0,esk3_0)
    | esk3_0 != k2_yellow_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( r1_lattice3(esk2_0,esk4_0,esk5_0)
    | k2_yellow_0(esk2_0,esk4_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    | k2_yellow_0(esk2_0,esk4_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk4_0) != esk3_0
    | ~ r1_orders_2(esk2_0,esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_0,X1)
    | k2_yellow_0(esk2_0,esk4_0) != esk3_0
    | X1 != k2_yellow_0(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14]),c_0_8]),c_0_10])]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk3_0)
    | esk3_0 = k2_yellow_0(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,esk4_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X3,esk1_3(X2,X1,X3))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk4_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13])])).

cnf(c_0_29,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,esk1_3(X2,X1,X3),X1)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,negated_conjecture,
    ( X1 = k2_yellow_0(esk2_0,esk4_0)
    | r1_orders_2(esk2_0,esk1_3(esk2_0,X1,esk4_0),esk3_0)
    | ~ r1_lattice3(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(esk1_3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_8]),c_0_10])]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_18]),c_0_13]),c_0_8]),c_0_10])]),c_0_28])).

cnf(c_0_32,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_18]),c_0_13]),c_0_8]),c_0_10])]),c_0_28]),
    [proof]).

%------------------------------------------------------------------------------
