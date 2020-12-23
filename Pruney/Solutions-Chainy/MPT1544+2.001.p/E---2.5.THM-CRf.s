%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 (6849 expanded)
%              Number of clauses        :   61 (2307 expanded)
%              Number of leaves         :    4 (1614 expanded)
%              Depth                    :   11
%              Number of atoms          :  442 (91641 expanded)
%              Number of equality atoms :   60 (13959 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   74 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l26_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k10_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(t22_yellow_0,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k13_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(c_0_4,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( r1_orders_2(X7,X8,X10)
        | X10 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v1_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,X10)
        | X10 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v1_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X11)
        | ~ r1_orders_2(X7,X9,X11)
        | r1_orders_2(X7,X10,X11)
        | X10 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v1_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | X10 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v1_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X8,esk1_4(X7,X8,X9,X10))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | X10 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v1_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | X10 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v1_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | X10 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v1_lattice3(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

fof(c_0_5,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v1_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X4 = k13_lattice3(X1,X2,X3)
                    <=> ( r1_orders_2(X1,X2,X4)
                        & r1_orders_2(X1,X3,X4)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_orders_2(X1,X2,X5)
                                & r1_orders_2(X1,X3,X5) )
                             => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_yellow_0])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))
    | X4 = k10_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    ! [X21] :
      ( v5_orders_2(esk2_0)
      & v1_lattice3(esk2_0)
      & l1_orders_2(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
      & ( m1_subset_1(esk6_0,u1_struct_0(esk2_0))
        | ~ r1_orders_2(esk2_0,esk3_0,esk5_0)
        | ~ r1_orders_2(esk2_0,esk4_0,esk5_0)
        | esk5_0 != k13_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( r1_orders_2(esk2_0,esk3_0,esk6_0)
        | ~ r1_orders_2(esk2_0,esk3_0,esk5_0)
        | ~ r1_orders_2(esk2_0,esk4_0,esk5_0)
        | esk5_0 != k13_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( r1_orders_2(esk2_0,esk4_0,esk6_0)
        | ~ r1_orders_2(esk2_0,esk3_0,esk5_0)
        | ~ r1_orders_2(esk2_0,esk4_0,esk5_0)
        | esk5_0 != k13_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( ~ r1_orders_2(esk2_0,esk5_0,esk6_0)
        | ~ r1_orders_2(esk2_0,esk3_0,esk5_0)
        | ~ r1_orders_2(esk2_0,esk4_0,esk5_0)
        | esk5_0 != k13_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( r1_orders_2(esk2_0,esk3_0,esk5_0)
        | esk5_0 = k13_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( r1_orders_2(esk2_0,esk4_0,esk5_0)
        | esk5_0 = k13_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( ~ m1_subset_1(X21,u1_struct_0(esk2_0))
        | ~ r1_orders_2(esk2_0,esk3_0,X21)
        | ~ r1_orders_2(esk2_0,esk4_0,X21)
        | r1_orders_2(esk2_0,esk5_0,X21)
        | esk5_0 = k13_lattice3(esk2_0,esk3_0,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ~ v5_orders_2(X13)
      | ~ v1_lattice3(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | k13_lattice3(X13,X14,X15) = k10_lattice3(X13,X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

cnf(c_0_11,plain,
    ( X2 = k10_lattice3(X1,X3,X4)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X2))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X2,X3,X4))
    | X4 = k10_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X3,X2,X4))
    | X4 = k10_lattice3(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | m1_subset_1(esk1_4(X2,X3,X4,X1),u1_struct_0(X2))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,X1,esk1_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_11,c_0_8])).

cnf(c_0_22,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X3,esk1_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_12,c_0_8])).

cnf(c_0_23,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X4,esk1_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,X2) = esk5_0
    | m1_subset_1(esk1_4(esk2_0,X1,X2,esk5_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X2,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk5_0)
    | esk5_0 = k13_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,esk4_0) = k13_lattice3(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k10_lattice3(esk2_0,X2,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X2,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ r1_orders_2(esk2_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_29,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,X2) = esk5_0
    | r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,X2,esk5_0))
    | ~ r1_orders_2(esk2_0,X2,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_30,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,X2) = esk5_0
    | r1_orders_2(esk2_0,X2,esk1_4(esk2_0,X1,X2,esk5_0))
    | ~ r1_orders_2(esk2_0,X1,esk5_0)
    | ~ r1_orders_2(esk2_0,X2,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_32,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k10_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | m1_subset_1(esk1_4(esk2_0,X1,esk4_0,esk5_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20])])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk5_0)
    | esk5_0 = k13_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( k10_lattice3(esk2_0,esk3_0,esk4_0) = k13_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k10_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk5_0,esk1_4(esk2_0,X1,esk4_0,esk5_0))
    | ~ r1_orders_2(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_15])])).

cnf(c_0_36,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,esk4_0,esk5_0))
    | ~ r1_orders_2(esk2_0,esk4_0,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( k10_lattice3(esk2_0,esk3_0,X1) = esk5_0
    | r1_orders_2(esk2_0,X1,esk1_4(esk2_0,esk3_0,X1,esk5_0))
    | ~ r1_orders_2(esk2_0,esk3_0,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_39,plain,
    ( r1_orders_2(X2,X5,X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k10_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_40,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31,c_0_8])])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_0,X1)
    | esk5_0 = k13_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ r1_orders_2(esk2_0,esk4_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | m1_subset_1(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_27])])).

cnf(c_0_43,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk5_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_34]),c_0_27])])).

cnf(c_0_44,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k10_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,esk4_0,esk5_0))
    | ~ r1_orders_2(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k10_lattice3(esk2_0,esk3_0,X1) = esk5_0
    | r1_orders_2(esk2_0,X1,esk1_4(esk2_0,esk3_0,X1,esk5_0))
    | ~ r1_orders_2(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_38,c_0_8])])).

cnf(c_0_47,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_39,c_0_8])])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,X1,esk4_0))
    | ~ m1_subset_1(k10_lattice3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_20]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_49,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk3_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0))
    | ~ r1_orders_2(esk2_0,esk4_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk3_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_34])]),c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk4_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_20]),c_0_34])]),c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,esk3_0,X1))
    | ~ m1_subset_1(k10_lattice3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk2_0,k10_lattice3(esk2_0,X1,esk4_0),X2)
    | ~ r1_orders_2(esk2_0,esk4_0,X2)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(k10_lattice3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_20]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,k13_lattice3(esk2_0,esk3_0,esk4_0))
    | ~ m1_subset_1(k13_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_27]),c_0_34]),c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,k13_lattice3(esk2_0,esk3_0,esk4_0))
    | ~ m1_subset_1(k13_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_20]),c_0_34]),c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk2_0,k13_lattice3(esk2_0,esk3_0,esk4_0),X1)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(k13_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_27]),c_0_34]),c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,esk3_0,esk5_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk5_0)
    | esk5_0 != k13_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55]),c_0_15])])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_55]),c_0_55]),c_0_15])])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk6_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk5_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk5_0)
    | esk5_0 != k13_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk6_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk5_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk5_0)
    | esk5_0 != k13_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk5_0,esk6_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk5_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk5_0)
    | esk5_0 != k13_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_0,X1)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_55]),c_0_55]),c_0_15])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_55])]),c_0_59]),c_0_60])])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_55])]),c_0_59]),c_0_60])])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_55])]),c_0_59]),c_0_60])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_55])]),c_0_59]),c_0_60])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67])]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.41  # and selection function SelectNewComplexAHP.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(l26_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k10_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 0.20/0.41  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.20/0.41  fof(t22_yellow_0, conjecture, ![X1]:(((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k13_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_yellow_0)).
% 0.20/0.41  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.20/0.41  fof(c_0_4, plain, ![X7, X8, X9, X10, X11]:((((r1_orders_2(X7,X8,X10)|X10!=k10_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v1_lattice3(X7)|~l1_orders_2(X7)))&(r1_orders_2(X7,X9,X10)|X10!=k10_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v1_lattice3(X7)|~l1_orders_2(X7))))&(~m1_subset_1(X11,u1_struct_0(X7))|(~r1_orders_2(X7,X8,X11)|~r1_orders_2(X7,X9,X11)|r1_orders_2(X7,X10,X11))|X10!=k10_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v1_lattice3(X7)|~l1_orders_2(X7))))&((m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))|(~r1_orders_2(X7,X8,X10)|~r1_orders_2(X7,X9,X10))|X10=k10_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v1_lattice3(X7)|~l1_orders_2(X7)))&(((r1_orders_2(X7,X8,esk1_4(X7,X8,X9,X10))|(~r1_orders_2(X7,X8,X10)|~r1_orders_2(X7,X9,X10))|X10=k10_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v1_lattice3(X7)|~l1_orders_2(X7)))&(r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))|(~r1_orders_2(X7,X8,X10)|~r1_orders_2(X7,X9,X10))|X10=k10_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v1_lattice3(X7)|~l1_orders_2(X7))))&(~r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))|(~r1_orders_2(X7,X8,X10)|~r1_orders_2(X7,X9,X10))|X10=k10_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v1_lattice3(X7)|~l1_orders_2(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).
% 0.20/0.41  fof(c_0_5, plain, ![X6]:(~l1_orders_2(X6)|(~v1_lattice3(X6)|~v2_struct_0(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.20/0.41  fof(c_0_6, negated_conjecture, ~(![X1]:(((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k13_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))))))), inference(assume_negation,[status(cth)],[t22_yellow_0])).
% 0.20/0.41  cnf(c_0_7, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))|X4=k10_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.41  cnf(c_0_8, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.41  fof(c_0_9, negated_conjecture, ![X21]:(((v5_orders_2(esk2_0)&v1_lattice3(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(esk2_0))&(((m1_subset_1(esk6_0,u1_struct_0(esk2_0))|(~r1_orders_2(esk2_0,esk3_0,esk5_0)|~r1_orders_2(esk2_0,esk4_0,esk5_0))|esk5_0!=k13_lattice3(esk2_0,esk3_0,esk4_0))&(((r1_orders_2(esk2_0,esk3_0,esk6_0)|(~r1_orders_2(esk2_0,esk3_0,esk5_0)|~r1_orders_2(esk2_0,esk4_0,esk5_0))|esk5_0!=k13_lattice3(esk2_0,esk3_0,esk4_0))&(r1_orders_2(esk2_0,esk4_0,esk6_0)|(~r1_orders_2(esk2_0,esk3_0,esk5_0)|~r1_orders_2(esk2_0,esk4_0,esk5_0))|esk5_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)))&(~r1_orders_2(esk2_0,esk5_0,esk6_0)|(~r1_orders_2(esk2_0,esk3_0,esk5_0)|~r1_orders_2(esk2_0,esk4_0,esk5_0))|esk5_0!=k13_lattice3(esk2_0,esk3_0,esk4_0))))&(((r1_orders_2(esk2_0,esk3_0,esk5_0)|esk5_0=k13_lattice3(esk2_0,esk3_0,esk4_0))&(r1_orders_2(esk2_0,esk4_0,esk5_0)|esk5_0=k13_lattice3(esk2_0,esk3_0,esk4_0)))&(~m1_subset_1(X21,u1_struct_0(esk2_0))|(~r1_orders_2(esk2_0,esk3_0,X21)|~r1_orders_2(esk2_0,esk4_0,X21)|r1_orders_2(esk2_0,esk5_0,X21))|esk5_0=k13_lattice3(esk2_0,esk3_0,esk4_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.20/0.41  fof(c_0_10, plain, ![X13, X14, X15]:(~v5_orders_2(X13)|~v1_lattice3(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))|k13_lattice3(X13,X14,X15)=k10_lattice3(X13,X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.20/0.41  cnf(c_0_11, plain, (X2=k10_lattice3(X1,X3,X4)|v2_struct_0(X1)|~r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X2))|~r1_orders_2(X1,X3,X2)|~r1_orders_2(X1,X4,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.41  cnf(c_0_12, plain, (r1_orders_2(X1,X2,esk1_4(X1,X2,X3,X4))|X4=k10_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.41  cnf(c_0_13, plain, (r1_orders_2(X1,X2,esk1_4(X1,X3,X2,X4))|X4=k10_lattice3(X1,X3,X2)|v2_struct_0(X1)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.41  cnf(c_0_14, plain, (X1=k10_lattice3(X2,X3,X4)|m1_subset_1(esk1_4(X2,X3,X4,X1),u1_struct_0(X2))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_7, c_0_8])).
% 0.20/0.41  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_17, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_19, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_21, plain, (X1=k10_lattice3(X2,X3,X4)|~r1_orders_2(X2,X1,esk1_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_11, c_0_8])).
% 0.20/0.41  cnf(c_0_22, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X3,esk1_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_12, c_0_8])).
% 0.20/0.41  cnf(c_0_23, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X4,esk1_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_13, c_0_8])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (k10_lattice3(esk2_0,X1,X2)=esk5_0|m1_subset_1(esk1_4(esk2_0,X1,X2,esk5_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X2,esk5_0)|~r1_orders_2(esk2_0,X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk5_0)|esk5_0=k13_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (k10_lattice3(esk2_0,X1,esk4_0)=k13_lattice3(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (X1=k10_lattice3(esk2_0,X2,esk4_0)|~r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X2,esk4_0,X1))|~r1_orders_2(esk2_0,esk4_0,X1)|~r1_orders_2(esk2_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (k10_lattice3(esk2_0,X1,X2)=esk5_0|r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,X2,esk5_0))|~r1_orders_2(esk2_0,X2,esk5_0)|~r1_orders_2(esk2_0,X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_15]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (k10_lattice3(esk2_0,X1,X2)=esk5_0|r1_orders_2(esk2_0,X2,esk1_4(esk2_0,X1,X2,esk5_0))|~r1_orders_2(esk2_0,X1,esk5_0)|~r1_orders_2(esk2_0,X2,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_15]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.41  cnf(c_0_31, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k10_lattice3(esk2_0,X1,esk4_0)=esk5_0|m1_subset_1(esk1_4(esk2_0,X1,esk4_0,esk5_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20])])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk5_0)|esk5_0=k13_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (k10_lattice3(esk2_0,esk3_0,esk4_0)=k13_lattice3(esk2_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k10_lattice3(esk2_0,X1,esk4_0)=esk5_0|~r1_orders_2(esk2_0,esk5_0,esk1_4(esk2_0,X1,esk4_0,esk5_0))|~r1_orders_2(esk2_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_15])])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (k10_lattice3(esk2_0,X1,esk4_0)=esk5_0|r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,esk4_0,esk5_0))|~r1_orders_2(esk2_0,esk4_0,esk5_0)|~r1_orders_2(esk2_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (k10_lattice3(esk2_0,esk3_0,X1)=esk5_0|r1_orders_2(esk2_0,X1,esk1_4(esk2_0,esk3_0,X1,esk5_0))|~r1_orders_2(esk2_0,esk3_0,esk5_0)|~r1_orders_2(esk2_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.20/0.41  cnf(c_0_38, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.41  cnf(c_0_39, plain, (r1_orders_2(X2,X5,X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|X5!=k10_lattice3(X2,X3,X4)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.41  cnf(c_0_40, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))|~m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31, c_0_8])])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (r1_orders_2(esk2_0,esk5_0,X1)|esk5_0=k13_lattice3(esk2_0,esk3_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,esk3_0,X1)|~r1_orders_2(esk2_0,esk4_0,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|m1_subset_1(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_27])])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|~r1_orders_2(esk2_0,esk5_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_33]), c_0_34]), c_0_27])])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k10_lattice3(esk2_0,X1,esk4_0)=esk5_0|r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,esk4_0,esk5_0))|~r1_orders_2(esk2_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k10_lattice3(esk2_0,esk3_0,X1)=esk5_0|r1_orders_2(esk2_0,X1,esk1_4(esk2_0,esk3_0,X1,esk5_0))|~r1_orders_2(esk2_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_37, c_0_33])).
% 0.20/0.41  cnf(c_0_46, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))|~m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_38, c_0_8])])).
% 0.20/0.41  cnf(c_0_47, plain, (r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_39, c_0_8])])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,X1,esk4_0))|~m1_subset_1(k10_lattice3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_20]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|~r1_orders_2(esk2_0,esk3_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0))|~r1_orders_2(esk2_0,esk4_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk3_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_34])]), c_0_33])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk4_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_20]), c_0_34])]), c_0_25])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,esk3_0,X1))|~m1_subset_1(k10_lattice3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_27]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (r1_orders_2(esk2_0,k10_lattice3(esk2_0,X1,esk4_0),X2)|~r1_orders_2(esk2_0,esk4_0,X2)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(k10_lattice3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_20]), c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,k13_lattice3(esk2_0,esk3_0,esk4_0))|~m1_subset_1(k13_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_27]), c_0_34]), c_0_34])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,k13_lattice3(esk2_0,esk3_0,esk4_0))|~m1_subset_1(k13_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_20]), c_0_34]), c_0_34])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk2_0,k13_lattice3(esk2_0,esk3_0,esk4_0),X1)|~r1_orders_2(esk2_0,esk4_0,X1)|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(k13_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_27]), c_0_34]), c_0_34])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,esk3_0,esk5_0)|~r1_orders_2(esk2_0,esk4_0,esk5_0)|esk5_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_55]), c_0_15])])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_55]), c_0_55]), c_0_15])])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk6_0)|~r1_orders_2(esk2_0,esk3_0,esk5_0)|~r1_orders_2(esk2_0,esk4_0,esk5_0)|esk5_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk6_0)|~r1_orders_2(esk2_0,esk3_0,esk5_0)|~r1_orders_2(esk2_0,esk4_0,esk5_0)|esk5_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (~r1_orders_2(esk2_0,esk5_0,esk6_0)|~r1_orders_2(esk2_0,esk3_0,esk5_0)|~r1_orders_2(esk2_0,esk4_0,esk5_0)|esk5_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (r1_orders_2(esk2_0,esk5_0,X1)|~r1_orders_2(esk2_0,esk4_0,X1)|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_55]), c_0_55]), c_0_15])])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_55])]), c_0_59]), c_0_60])])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_55])]), c_0_59]), c_0_60])])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_55])]), c_0_59]), c_0_60])])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (~r1_orders_2(esk2_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_55])]), c_0_59]), c_0_60])])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67])]), c_0_68]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 70
% 0.20/0.41  # Proof object clause steps            : 61
% 0.20/0.41  # Proof object formula steps           : 9
% 0.20/0.41  # Proof object conjectures             : 48
% 0.20/0.41  # Proof object clause conjectures      : 45
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 22
% 0.20/0.41  # Proof object initial formulas used   : 4
% 0.20/0.41  # Proof object generating inferences   : 25
% 0.20/0.41  # Proof object simplifying inferences  : 102
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 4
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 22
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 22
% 0.20/0.41  # Processed clauses                    : 281
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 19
% 0.20/0.41  # ...remaining for further processing  : 262
% 0.20/0.41  # Other redundant clauses eliminated   : 3
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 49
% 0.20/0.41  # Backward-rewritten                   : 88
% 0.20/0.41  # Generated clauses                    : 761
% 0.20/0.41  # ...of the previous two non-trivial   : 775
% 0.20/0.41  # Contextual simplify-reflections      : 50
% 0.20/0.41  # Paramodulations                      : 758
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 3
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 100
% 0.20/0.41  #    Positive orientable unit clauses  : 23
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 76
% 0.20/0.41  # Current number of unprocessed clauses: 444
% 0.20/0.41  # ...number of literals in the above   : 2204
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 159
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 2865
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 424
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 111
% 0.20/0.41  # Unit Clause-clause subsumption calls : 260
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 110
% 0.20/0.41  # BW rewrite match successes           : 14
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 29412
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.060 s
% 0.20/0.41  # System time              : 0.003 s
% 0.20/0.41  # Total time               : 0.063 s
% 0.20/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
