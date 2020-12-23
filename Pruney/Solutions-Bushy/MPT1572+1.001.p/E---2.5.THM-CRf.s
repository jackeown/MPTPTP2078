%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1572+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:25 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   75 (3462027 expanded)
%              Number of clauses        :   66 (1162675 expanded)
%              Number of leaves         :    4 (843817 expanded)
%              Depth                    :   37
%              Number of atoms          :  386 (62548434 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   66 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( r1_yellow_0(X1,X2)
           => r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
          & ( r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
           => r1_yellow_0(X1,X2) )
          & ( r2_yellow_0(X1,X2)
           => r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
          & ( r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
           => r2_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_yellow_0)).

fof(t48_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) )
            & r2_yellow_0(X1,X2) )
         => r2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_yellow_0)).

fof(t5_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( ( r2_lattice3(X1,X2,X3)
             => r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3) )
            & ( r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
             => r2_lattice3(X1,X2,X3) )
            & ( r1_lattice3(X1,X2,X3)
             => r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3) )
            & ( r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
             => r1_lattice3(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow_0)).

fof(t46_yellow_0,axiom,(
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

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( r1_yellow_0(X1,X2)
             => r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
            & ( r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
             => r1_yellow_0(X1,X2) )
            & ( r2_yellow_0(X1,X2)
             => r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
            & ( r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
             => r2_yellow_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_yellow_0])).

fof(c_0_5,plain,(
    ! [X9,X10,X11] :
      ( ( m1_subset_1(esk2_3(X9,X10,X11),u1_struct_0(X9))
        | ~ r2_yellow_0(X9,X10)
        | r2_yellow_0(X9,X11)
        | v2_struct_0(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ r1_lattice3(X9,X10,esk2_3(X9,X10,X11))
        | ~ r1_lattice3(X9,X11,esk2_3(X9,X10,X11))
        | ~ r2_yellow_0(X9,X10)
        | r2_yellow_0(X9,X11)
        | v2_struct_0(X9)
        | ~ l1_orders_2(X9) )
      & ( r1_lattice3(X9,X10,esk2_3(X9,X10,X11))
        | r1_lattice3(X9,X11,esk2_3(X9,X10,X11))
        | ~ r2_yellow_0(X9,X10)
        | r2_yellow_0(X9,X11)
        | v2_struct_0(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_yellow_0])])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_orders_2(esk3_0)
    & ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r2_yellow_0(esk3_0,esk4_0)
      | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r1_yellow_0(esk3_0,esk4_0) )
    & ( ~ r2_yellow_0(esk3_0,esk4_0)
      | r2_yellow_0(esk3_0,esk4_0)
      | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r1_yellow_0(esk3_0,esk4_0) )
    & ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r1_yellow_0(esk3_0,esk4_0) )
    & ( ~ r2_yellow_0(esk3_0,esk4_0)
      | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r1_yellow_0(esk3_0,esk4_0) )
    & ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r2_yellow_0(esk3_0,esk4_0)
      | ~ r1_yellow_0(esk3_0,esk4_0)
      | r1_yellow_0(esk3_0,esk4_0) )
    & ( ~ r2_yellow_0(esk3_0,esk4_0)
      | r2_yellow_0(esk3_0,esk4_0)
      | ~ r1_yellow_0(esk3_0,esk4_0)
      | r1_yellow_0(esk3_0,esk4_0) )
    & ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r1_yellow_0(esk3_0,esk4_0)
      | r1_yellow_0(esk3_0,esk4_0) )
    & ( ~ r2_yellow_0(esk3_0,esk4_0)
      | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r1_yellow_0(esk3_0,esk4_0)
      | r1_yellow_0(esk3_0,esk4_0) )
    & ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r2_yellow_0(esk3_0,esk4_0)
      | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) )
    & ( ~ r2_yellow_0(esk3_0,esk4_0)
      | r2_yellow_0(esk3_0,esk4_0)
      | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) )
    & ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) )
    & ( ~ r2_yellow_0(esk3_0,esk4_0)
      | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) )
    & ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | r2_yellow_0(esk3_0,esk4_0)
      | ~ r1_yellow_0(esk3_0,esk4_0)
      | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) )
    & ( ~ r2_yellow_0(esk3_0,esk4_0)
      | r2_yellow_0(esk3_0,esk4_0)
      | ~ r1_yellow_0(esk3_0,esk4_0)
      | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) )
    & ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r1_yellow_0(esk3_0,esk4_0)
      | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) )
    & ( ~ r2_yellow_0(esk3_0,esk4_0)
      | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
      | ~ r1_yellow_0(esk3_0,esk4_0)
      | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

fof(c_0_7,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r2_lattice3(X13,X14,X15)
        | r2_lattice3(X13,k3_xboole_0(X14,u1_struct_0(X13)),X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r2_lattice3(X13,k3_xboole_0(X14,u1_struct_0(X13)),X15)
        | r2_lattice3(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X15)
        | r1_lattice3(X13,k3_xboole_0(X14,u1_struct_0(X13)),X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,k3_xboole_0(X14,u1_struct_0(X13)),X15)
        | r1_lattice3(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_yellow_0])])])])])).

cnf(c_0_8,plain,
    ( r1_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | r1_lattice3(X1,X3,esk2_3(X1,X2,X3))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r2_yellow_0(esk3_0,esk4_0)
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r1_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r2_yellow_0(esk3_0,X1)
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_10])]),c_0_11]),c_0_15])).

cnf(c_0_17,plain,
    ( r1_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X3,esk2_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk4_0))
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(ef,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,k3_xboole_0(X2,u1_struct_0(esk3_0)),esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0)
    | ~ r1_lattice3(esk3_0,X2,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_10])]),c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0)
    | ~ r1_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_10])]),c_0_11]),c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk4_0,X1))
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_22]),c_0_10])]),c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_22]),c_0_10])]),c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0)
    | ~ r2_yellow_0(esk3_0,esk4_0)
    | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( r2_yellow_0(esk3_0,k3_xboole_0(X1,u1_struct_0(esk3_0)))
    | r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,k3_xboole_0(X1,u1_struct_0(esk3_0))))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk4_0,k3_xboole_0(X1,u1_struct_0(esk3_0))))
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_23]),c_0_10])]),c_0_11]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0)
    | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,k3_xboole_0(X2,u1_struct_0(esk3_0)),esk2_3(esk3_0,esk4_0,X1))
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0)
    | ~ r1_lattice3(esk3_0,X2,esk2_3(esk3_0,esk4_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_24]),c_0_10])]),c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))))
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_26]),c_0_27])).

fof(c_0_30,plain,(
    ! [X5,X6,X7] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | ~ r1_yellow_0(X5,X6)
        | r1_yellow_0(X5,X7)
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r2_lattice3(X5,X6,esk1_3(X5,X6,X7))
        | ~ r2_lattice3(X5,X7,esk1_3(X5,X6,X7))
        | ~ r1_yellow_0(X5,X6)
        | r1_yellow_0(X5,X7)
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_lattice3(X5,X6,esk1_3(X5,X6,X7))
        | r2_lattice3(X5,X7,esk1_3(X5,X6,X7))
        | ~ r1_yellow_0(X5,X6)
        | r1_yellow_0(X5,X7)
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_yellow_0])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( r1_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk2_3(esk3_0,esk4_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))))
    | r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_27])).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | r2_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | r1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r1_yellow_0(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_31]),c_0_10])]),c_0_11]),c_0_29]),c_0_22]),c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( r2_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0)
    | r1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk1_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | r2_lattice3(esk3_0,X1,esk1_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_10])]),c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0)
    | r1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk1_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_10])]),c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0)
    | r1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,esk4_0,esk1_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | r2_lattice3(esk3_0,X1,esk1_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_10])]),c_0_11]),c_0_37])).

cnf(c_0_39,plain,
    ( r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,plain,
    ( r1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0)
    | r2_lattice3(esk3_0,esk4_0,esk1_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk4_0)) ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0)
    | r1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,k3_xboole_0(X2,u1_struct_0(esk3_0)),esk1_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | ~ r2_lattice3(esk3_0,X2,esk1_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_10])]),c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0)
    | ~ r2_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk1_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_10])]),c_0_11]),c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( r1_yellow_0(esk3_0,X1)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_44]),c_0_10])]),c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( r1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,k3_xboole_0(X2,u1_struct_0(esk3_0)),esk1_3(esk3_0,esk4_0,X1))
    | ~ r2_lattice3(esk3_0,X2,esk1_3(esk3_0,esk4_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_45]),c_0_10])]),c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( r1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,esk4_0,esk1_3(esk3_0,esk4_0,X1))
    | r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_44]),c_0_10])]),c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( r1_yellow_0(esk3_0,X1)
    | r2_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk1_3(esk3_0,esk4_0,X1))
    | r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r2_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk1_3(esk3_0,esk4_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))) ),
    inference(ef,[status(thm)],[c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r2_yellow_0(esk3_0,esk4_0)
    | ~ r1_yellow_0(esk3_0,esk4_0)
    | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_51,negated_conjecture,
    ( r1_yellow_0(esk3_0,k3_xboole_0(X1,u1_struct_0(esk3_0)))
    | r2_lattice3(esk3_0,esk4_0,esk1_3(esk3_0,esk4_0,k3_xboole_0(X1,u1_struct_0(esk3_0))))
    | r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,k3_xboole_0(X1,u1_struct_0(esk3_0)))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_47]),c_0_10])]),c_0_11]),c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | ~ r2_lattice3(esk3_0,esk4_0,esk1_3(esk3_0,esk4_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_49]),c_0_44]),c_0_10])]),c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r2_yellow_0(esk3_0,esk4_0)
    | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_44])])).

cnf(c_0_54,negated_conjecture,
    ( r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_51]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | r2_yellow_0(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_56,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_55]),c_0_10])]),c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r2_yellow_0(esk3_0,X1)
    | m1_subset_1(esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_55]),c_0_10])]),c_0_11])).

cnf(c_0_58,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_56]),c_0_10])]),c_0_11]),c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk4_0)) ),
    inference(ef,[status(thm)],[c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,k3_xboole_0(X2,u1_struct_0(esk3_0)),esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1))
    | ~ r1_lattice3(esk3_0,X2,esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_57]),c_0_10])]),c_0_11])).

cnf(c_0_61,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0)
    | ~ r1_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk2_3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_59]),c_0_10])]),c_0_11]),c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_yellow_0(esk3_0,esk4_0)
    | ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | ~ r1_yellow_0(esk3_0,esk4_0)
    | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_64,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_62]),c_0_10])]),c_0_11])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | ~ r2_yellow_0(esk3_0,esk4_0)
    | ~ r1_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_44])])).

cnf(c_0_66,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,k3_xboole_0(X2,u1_struct_0(esk3_0)),esk2_3(esk3_0,esk4_0,X1))
    | ~ r1_lattice3(esk3_0,X2,esk2_3(esk3_0,esk4_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_64]),c_0_10])]),c_0_11])).

cnf(c_0_67,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk4_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_62]),c_0_10])]),c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))
    | ~ r2_yellow_0(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_54])])).

cnf(c_0_69,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk2_3(esk3_0,esk4_0,X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_yellow_0(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_62])])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattice3(esk3_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)),esk2_3(esk3_0,esk4_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_69]),c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_71]),c_0_62]),c_0_10])]),c_0_70]),c_0_11])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_subset_1(esk2_3(esk3_0,esk4_0,k3_xboole_0(esk4_0,u1_struct_0(esk3_0))),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_71]),c_0_10])]),c_0_11]),c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_64]),c_0_70]),
    [proof]).

%------------------------------------------------------------------------------
