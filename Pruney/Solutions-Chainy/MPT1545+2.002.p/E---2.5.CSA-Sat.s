%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:15 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 597 expanded)
%              Number of clauses        :   48 ( 191 expanded)
%              Number of leaves         :    3 ( 143 expanded)
%              Depth                    :    6
%              Number of atoms          :  201 (7541 expanded)
%              Number of equality atoms :   67 (1230 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_yellow_0,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k12_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(commutativity_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X4 = k12_lattice3(X1,X2,X3)
                    <=> ( r1_orders_2(X1,X4,X2)
                        & r1_orders_2(X1,X4,X3)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_orders_2(X1,X5,X2)
                                & r1_orders_2(X1,X5,X3) )
                             => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_yellow_0])).

fof(c_0_4,plain,(
    ! [X9,X10,X11] :
      ( ~ v5_orders_2(X9)
      | ~ v2_lattice3(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | k12_lattice3(X9,X10,X11) = k11_lattice3(X9,X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_5,negated_conjecture,(
    ! [X17] :
      ( v5_orders_2(esk1_0)
      & v2_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
      & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
      & ( m1_subset_1(esk5_0,u1_struct_0(esk1_0))
        | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
        | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
        | esk4_0 != k12_lattice3(esk1_0,esk2_0,esk3_0) )
      & ( r1_orders_2(esk1_0,esk5_0,esk2_0)
        | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
        | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
        | esk4_0 != k12_lattice3(esk1_0,esk2_0,esk3_0) )
      & ( r1_orders_2(esk1_0,esk5_0,esk3_0)
        | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
        | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
        | esk4_0 != k12_lattice3(esk1_0,esk2_0,esk3_0) )
      & ( ~ r1_orders_2(esk1_0,esk5_0,esk4_0)
        | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
        | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
        | esk4_0 != k12_lattice3(esk1_0,esk2_0,esk3_0) )
      & ( r1_orders_2(esk1_0,esk4_0,esk2_0)
        | esk4_0 = k12_lattice3(esk1_0,esk2_0,esk3_0) )
      & ( r1_orders_2(esk1_0,esk4_0,esk3_0)
        | esk4_0 = k12_lattice3(esk1_0,esk2_0,esk3_0) )
      & ( ~ m1_subset_1(X17,u1_struct_0(esk1_0))
        | ~ r1_orders_2(esk1_0,X17,esk2_0)
        | ~ r1_orders_2(esk1_0,X17,esk3_0)
        | r1_orders_2(esk1_0,X17,esk4_0)
        | esk4_0 = k12_lattice3(esk1_0,esk2_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8] :
      ( ~ v5_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k12_lattice3(X6,X7,X8) = k12_lattice3(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).

cnf(c_0_7,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_12,plain,
    ( k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
    | esk4_0 != k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( k11_lattice3(esk1_0,X1,esk2_0) = k12_lattice3(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk3_0) = k12_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_9]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( k11_lattice3(esk1_0,X1,esk4_0) = k12_lattice3(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_14]),c_0_9]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk4_0) = k12_lattice3(esk1_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_14]),c_0_9]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( k11_lattice3(esk1_0,X1,esk5_0) = k12_lattice3(esk1_0,X1,esk5_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_15]),c_0_9]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( k11_lattice3(esk1_0,X1,esk3_0) = k12_lattice3(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_13]),c_0_9]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk5_0) = k12_lattice3(esk1_0,esk5_0,X1)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_15]),c_0_9]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( k11_lattice3(esk1_0,esk3_0,esk2_0) = k12_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( k12_lattice3(esk1_0,esk3_0,esk2_0) = k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_8]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk4_0) = k12_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( k12_lattice3(esk1_0,esk2_0,esk4_0) = k12_lattice3(esk1_0,esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_8]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( k11_lattice3(esk1_0,esk3_0,esk4_0) = k12_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( k12_lattice3(esk1_0,esk3_0,esk4_0) = k12_lattice3(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_13]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk5_0) = k12_lattice3(esk1_0,esk2_0,esk5_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_8]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( k11_lattice3(esk1_0,esk3_0,esk5_0) = k12_lattice3(esk1_0,esk3_0,esk5_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( k11_lattice3(esk1_0,esk4_0,esk5_0) = k12_lattice3(esk1_0,esk4_0,esk5_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_14]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( k11_lattice3(esk1_0,esk5_0,esk5_0) = k12_lattice3(esk1_0,esk5_0,esk5_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( k11_lattice3(esk1_0,esk5_0,esk2_0) = k12_lattice3(esk1_0,esk5_0,esk2_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( k11_lattice3(esk1_0,esk5_0,esk3_0) = k12_lattice3(esk1_0,esk5_0,esk3_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_15]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( k12_lattice3(esk1_0,esk5_0,esk2_0) = k12_lattice3(esk1_0,esk2_0,esk5_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_8]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( k12_lattice3(esk1_0,esk5_0,esk3_0) = k12_lattice3(esk1_0,esk3_0,esk5_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( k11_lattice3(esk1_0,esk5_0,esk4_0) = k12_lattice3(esk1_0,esk5_0,esk4_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk2_0) = k12_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_8]),c_0_9]),c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( k12_lattice3(esk1_0,esk5_0,esk4_0) = k12_lattice3(esk1_0,esk4_0,esk5_0)
    | k12_lattice3(esk1_0,esk2_0,esk3_0) != esk4_0
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_15]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | esk4_0 = k12_lattice3(esk1_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk1_0,esk5_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
    | esk4_0 != k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk1_0,esk5_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
    | esk4_0 != k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk3_0)
    | esk4_0 = k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk2_0)
    | esk4_0 = k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk5_0,esk4_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk3_0)
    | esk4_0 != k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( k11_lattice3(esk1_0,esk3_0,esk2_0) = k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk4_0) = k12_lattice3(esk1_0,esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( k11_lattice3(esk1_0,esk3_0,esk4_0) = k12_lattice3(esk1_0,esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk2_0) = k12_lattice3(esk1_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_8]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( k11_lattice3(esk1_0,esk4_0,esk2_0) = k12_lattice3(esk1_0,esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk3_0) = k12_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_8]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( k11_lattice3(esk1_0,esk3_0,esk3_0) = k12_lattice3(esk1_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( k11_lattice3(esk1_0,esk4_0,esk3_0) = k12_lattice3(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( k11_lattice3(esk1_0,esk4_0,esk4_0) = k12_lattice3(esk1_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:01:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # No proof found!
% 0.12/0.37  # SZS status CounterSatisfiable
% 0.12/0.37  # SZS output start Saturation
% 0.12/0.37  fof(t23_yellow_0, conjecture, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k12_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow_0)).
% 0.12/0.37  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.12/0.38  fof(commutativity_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k12_lattice3(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k12_lattice3)).
% 0.12/0.38  fof(c_0_3, negated_conjecture, ~(![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k12_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4)))))))))), inference(assume_negation,[status(cth)],[t23_yellow_0])).
% 0.12/0.38  fof(c_0_4, plain, ![X9, X10, X11]:(~v5_orders_2(X9)|~v2_lattice3(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|k12_lattice3(X9,X10,X11)=k11_lattice3(X9,X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.12/0.38  fof(c_0_5, negated_conjecture, ![X17]:(((v5_orders_2(esk1_0)&v2_lattice3(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(m1_subset_1(esk4_0,u1_struct_0(esk1_0))&(((m1_subset_1(esk5_0,u1_struct_0(esk1_0))|(~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0))|esk4_0!=k12_lattice3(esk1_0,esk2_0,esk3_0))&(((r1_orders_2(esk1_0,esk5_0,esk2_0)|(~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0))|esk4_0!=k12_lattice3(esk1_0,esk2_0,esk3_0))&(r1_orders_2(esk1_0,esk5_0,esk3_0)|(~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0))|esk4_0!=k12_lattice3(esk1_0,esk2_0,esk3_0)))&(~r1_orders_2(esk1_0,esk5_0,esk4_0)|(~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0))|esk4_0!=k12_lattice3(esk1_0,esk2_0,esk3_0))))&(((r1_orders_2(esk1_0,esk4_0,esk2_0)|esk4_0=k12_lattice3(esk1_0,esk2_0,esk3_0))&(r1_orders_2(esk1_0,esk4_0,esk3_0)|esk4_0=k12_lattice3(esk1_0,esk2_0,esk3_0)))&(~m1_subset_1(X17,u1_struct_0(esk1_0))|(~r1_orders_2(esk1_0,X17,esk2_0)|~r1_orders_2(esk1_0,X17,esk3_0)|r1_orders_2(esk1_0,X17,esk4_0))|esk4_0=k12_lattice3(esk1_0,esk2_0,esk3_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).
% 0.12/0.38  fof(c_0_6, plain, ![X6, X7, X8]:(~v5_orders_2(X6)|~v2_lattice3(X6)|~l1_orders_2(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))|k12_lattice3(X6,X7,X8)=k12_lattice3(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).
% 0.12/0.38  cnf(c_0_7, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.38  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_9, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_10, negated_conjecture, (v2_lattice3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_11, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_12, plain, (k12_lattice3(X1,X2,X3)=k12_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.12/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk1_0))|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)|esk4_0!=k12_lattice3(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (k11_lattice3(esk1_0,X1,esk2_0)=k12_lattice3(esk1_0,X1,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11])]), ['final']).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (k12_lattice3(esk1_0,X1,esk3_0)=k12_lattice3(esk1_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_9]), c_0_10]), c_0_11])]), ['final']).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (k11_lattice3(esk1_0,X1,esk4_0)=k12_lattice3(esk1_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_14]), c_0_9]), c_0_10]), c_0_11])]), ['final']).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (k12_lattice3(esk1_0,X1,esk4_0)=k12_lattice3(esk1_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_14]), c_0_9]), c_0_10]), c_0_11])]), ['final']).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (k11_lattice3(esk1_0,X1,esk5_0)=k12_lattice3(esk1_0,X1,esk5_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_15]), c_0_9]), c_0_10]), c_0_11])]), ['final']).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (k11_lattice3(esk1_0,X1,esk3_0)=k12_lattice3(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_13]), c_0_9]), c_0_10]), c_0_11])]), ['final']).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (k12_lattice3(esk1_0,X1,esk5_0)=k12_lattice3(esk1_0,esk5_0,X1)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_15]), c_0_9]), c_0_10]), c_0_11])]), ['final']).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (k11_lattice3(esk1_0,esk3_0,esk2_0)=k12_lattice3(esk1_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_13])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (k12_lattice3(esk1_0,esk3_0,esk2_0)=k12_lattice3(esk1_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_8]), ['final']).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (k11_lattice3(esk1_0,esk2_0,esk4_0)=k12_lattice3(esk1_0,esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_8])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (k12_lattice3(esk1_0,esk2_0,esk4_0)=k12_lattice3(esk1_0,esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_8]), ['final']).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (k11_lattice3(esk1_0,esk3_0,esk4_0)=k12_lattice3(esk1_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (k12_lattice3(esk1_0,esk3_0,esk4_0)=k12_lattice3(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_13]), ['final']).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (k11_lattice3(esk1_0,esk2_0,esk5_0)=k12_lattice3(esk1_0,esk2_0,esk5_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_8]), ['final']).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (k11_lattice3(esk1_0,esk3_0,esk5_0)=k12_lattice3(esk1_0,esk3_0,esk5_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_13]), ['final']).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (k11_lattice3(esk1_0,esk4_0,esk5_0)=k12_lattice3(esk1_0,esk4_0,esk5_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (k11_lattice3(esk1_0,esk5_0,esk5_0)=k12_lattice3(esk1_0,esk5_0,esk5_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_15]), ['final']).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (k11_lattice3(esk1_0,esk5_0,esk2_0)=k12_lattice3(esk1_0,esk5_0,esk2_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_15]), ['final']).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (k11_lattice3(esk1_0,esk5_0,esk3_0)=k12_lattice3(esk1_0,esk5_0,esk3_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_15]), ['final']).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (k12_lattice3(esk1_0,esk5_0,esk2_0)=k12_lattice3(esk1_0,esk2_0,esk5_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_8]), ['final']).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (k12_lattice3(esk1_0,esk5_0,esk3_0)=k12_lattice3(esk1_0,esk3_0,esk5_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_13]), ['final']).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (k11_lattice3(esk1_0,esk5_0,esk4_0)=k12_lattice3(esk1_0,esk5_0,esk4_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_15]), ['final']).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (k12_lattice3(esk1_0,X1,esk2_0)=k12_lattice3(esk1_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_8]), c_0_9]), c_0_10]), c_0_11])]), ['final']).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (k12_lattice3(esk1_0,esk5_0,esk4_0)=k12_lattice3(esk1_0,esk4_0,esk5_0)|k12_lattice3(esk1_0,esk2_0,esk3_0)!=esk4_0|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_15]), ['final']).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (r1_orders_2(esk1_0,X1,esk4_0)|esk4_0=k12_lattice3(esk1_0,esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~r1_orders_2(esk1_0,X1,esk2_0)|~r1_orders_2(esk1_0,X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (r1_orders_2(esk1_0,esk5_0,esk3_0)|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)|esk4_0!=k12_lattice3(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (r1_orders_2(esk1_0,esk5_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)|esk4_0!=k12_lattice3(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk1_0,esk4_0,esk3_0)|esk4_0=k12_lattice3(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (r1_orders_2(esk1_0,esk4_0,esk2_0)|esk4_0=k12_lattice3(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (~r1_orders_2(esk1_0,esk5_0,esk4_0)|~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,esk3_0)|esk4_0!=k12_lattice3(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (k11_lattice3(esk1_0,esk3_0,esk2_0)=k12_lattice3(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_23, c_0_24]), ['final']).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (k11_lattice3(esk1_0,esk2_0,esk4_0)=k12_lattice3(esk1_0,esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (k11_lattice3(esk1_0,esk3_0,esk4_0)=k12_lattice3(esk1_0,esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (k11_lattice3(esk1_0,esk2_0,esk2_0)=k12_lattice3(esk1_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_8]), ['final']).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (k11_lattice3(esk1_0,esk4_0,esk2_0)=k12_lattice3(esk1_0,esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, (k11_lattice3(esk1_0,esk2_0,esk3_0)=k12_lattice3(esk1_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_8]), ['final']).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (k11_lattice3(esk1_0,esk3_0,esk3_0)=k12_lattice3(esk1_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_13]), ['final']).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (k11_lattice3(esk1_0,esk4_0,esk3_0)=k12_lattice3(esk1_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (k11_lattice3(esk1_0,esk4_0,esk4_0)=k12_lattice3(esk1_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_14]), ['final']).
% 0.12/0.38  # SZS output end Saturation
% 0.12/0.38  # Proof object total steps             : 55
% 0.12/0.38  # Proof object clause steps            : 48
% 0.12/0.38  # Proof object formula steps           : 7
% 0.12/0.38  # Proof object conjectures             : 49
% 0.12/0.38  # Proof object clause conjectures      : 46
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 15
% 0.12/0.38  # Proof object initial formulas used   : 3
% 0.12/0.38  # Proof object generating inferences   : 30
% 0.12/0.38  # Proof object simplifying inferences  : 35
% 0.12/0.38  # Parsed axioms                        : 3
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 15
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 15
% 0.12/0.38  # Processed clauses                    : 66
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 3
% 0.12/0.38  # ...remaining for further processing  : 63
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 3
% 0.12/0.38  # Generated clauses                    : 42
% 0.12/0.38  # ...of the previous two non-trivial   : 36
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 42
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 45
% 0.12/0.38  #    Positive orientable unit clauses  : 18
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 27
% 0.12/0.38  # Current number of unprocessed clauses: 0
% 0.12/0.38  # ...number of literals in the above   : 0
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 18
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 44
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 6
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.38  # Unit Clause-clause subsumption calls : 6
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 25
% 0.12/0.38  # BW rewrite match successes           : 3
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 2589
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.027 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.034 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
