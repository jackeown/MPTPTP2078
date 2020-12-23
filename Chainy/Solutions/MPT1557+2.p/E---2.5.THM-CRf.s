%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1557+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:06 EST 2020

% Result     : Theorem 14.14s
% Output     : CNFRefutation 14.14s
% Verified   : 
% Statistics : Number of formulae       :   25 (  65 expanded)
%              Number of clauses        :   16 (  24 expanded)
%              Number of leaves         :    4 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  112 ( 293 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_yellow_0(X1,X2)
           => ( X3 = k2_yellow_0(X1,X2)
            <=> ( r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(t35_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r2_yellow_0(X1,X2)
            & r2_yellow_0(X1,X3) )
         => r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow_0)).

fof(t9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,X3,X4)
                 => r1_lattice3(X1,X2,X4) )
                & ( r2_lattice3(X1,X3,X4)
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(c_0_4,plain,(
    ! [X9452,X9453,X9454,X9455] :
      ( ( r1_lattice3(X9452,X9453,X9454)
        | X9454 != k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) )
      & ( ~ m1_subset_1(X9455,u1_struct_0(X9452))
        | ~ r1_lattice3(X9452,X9453,X9455)
        | r1_orders_2(X9452,X9455,X9454)
        | X9454 != k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) )
      & ( m1_subset_1(esk1068_3(X9452,X9453,X9454),u1_struct_0(X9452))
        | ~ r1_lattice3(X9452,X9453,X9454)
        | X9454 = k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) )
      & ( r1_lattice3(X9452,X9453,esk1068_3(X9452,X9453,X9454))
        | ~ r1_lattice3(X9452,X9453,X9454)
        | X9454 = k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) )
      & ( ~ r1_orders_2(X9452,esk1068_3(X9452,X9453,X9454),X9454)
        | ~ r1_lattice3(X9452,X9453,X9454)
        | X9454 = k2_yellow_0(X9452,X9453)
        | ~ r2_yellow_0(X9452,X9453)
        | ~ m1_subset_1(X9454,u1_struct_0(X9452))
        | ~ l1_orders_2(X9452) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

fof(c_0_5,plain,(
    ! [X9495,X9496] :
      ( ~ l1_orders_2(X9495)
      | m1_subset_1(k2_yellow_0(X9495,X9496),u1_struct_0(X9495)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2,X3] :
            ( ( r1_tarski(X2,X3)
              & r2_yellow_0(X1,X2)
              & r2_yellow_0(X1,X3) )
           => r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t35_yellow_0])).

cnf(c_0_7,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1099_0)
    & r1_tarski(esk1100_0,esk1101_0)
    & r2_yellow_0(esk1099_0,esk1100_0)
    & r2_yellow_0(esk1099_0,esk1101_0)
    & ~ r1_orders_2(esk1099_0,k2_yellow_0(esk1099_0,esk1101_0),k2_yellow_0(esk1099_0,esk1100_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X9644,X9645,X9646,X9647] :
      ( ( ~ r1_lattice3(X9644,X9646,X9647)
        | r1_lattice3(X9644,X9645,X9647)
        | ~ m1_subset_1(X9647,u1_struct_0(X9644))
        | ~ r1_tarski(X9645,X9646)
        | ~ l1_orders_2(X9644) )
      & ( ~ r2_lattice3(X9644,X9646,X9647)
        | r2_lattice3(X9644,X9645,X9647)
        | ~ m1_subset_1(X9647,u1_struct_0(X9644))
        | ~ r1_tarski(X9645,X9646)
        | ~ l1_orders_2(X9644) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).

cnf(c_0_11,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_7]),c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r2_yellow_0(esk1099_0,esk1101_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1099_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_lattice3(X1,X4,X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_lattice3(esk1099_0,esk1101_0,k2_yellow_0(esk1099_0,esk1101_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(k2_yellow_0(esk1099_0,X1),u1_struct_0(esk1099_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_13])).

cnf(c_0_17,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( r1_lattice3(esk1099_0,X1,k2_yellow_0(esk1099_0,esk1101_0))
    | ~ r1_tarski(X1,esk1101_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_13]),c_0_16])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1100_0,esk1101_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk1099_0,esk1100_0,k2_yellow_0(esk1099_0,esk1101_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r2_yellow_0(esk1099_0,esk1100_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_orders_2(esk1099_0,k2_yellow_0(esk1099_0,esk1101_0),k2_yellow_0(esk1099_0,esk1100_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_13]),c_0_16])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
