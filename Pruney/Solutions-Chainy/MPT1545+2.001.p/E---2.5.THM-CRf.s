%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:15 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  120 (573959 expanded)
%              Number of clauses        :  111 (190289 expanded)
%              Number of leaves         :    4 (135534 expanded)
%              Depth                    :   19
%              Number of atoms          :  558 (7766827 expanded)
%              Number of equality atoms :  108 (1187577 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   74 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l28_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k11_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(c_0_4,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( r1_orders_2(X7,X10,X8)
        | X10 != k11_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X10,X9)
        | X10 != k11_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X11,X8)
        | ~ r1_orders_2(X7,X11,X9)
        | r1_orders_2(X7,X11,X10)
        | X10 != k11_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ r1_orders_2(X7,X10,X8)
        | ~ r1_orders_2(X7,X10,X9)
        | X10 = k11_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,esk1_4(X7,X8,X9,X10),X8)
        | ~ r1_orders_2(X7,X10,X8)
        | ~ r1_orders_2(X7,X10,X9)
        | X10 = k11_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,esk1_4(X7,X8,X9,X10),X9)
        | ~ r1_orders_2(X7,X10,X8)
        | ~ r1_orders_2(X7,X10,X9)
        | X10 = k11_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,esk1_4(X7,X8,X9,X10),X10)
        | ~ r1_orders_2(X7,X10,X8)
        | ~ r1_orders_2(X7,X10,X9)
        | X10 = k11_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v5_orders_2(X7)
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_5,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_6,negated_conjecture,(
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

cnf(c_0_7,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X3)
    | X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    ! [X21] :
      ( v5_orders_2(esk2_0)
      & v2_lattice3(esk2_0)
      & l1_orders_2(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
      & ( m1_subset_1(esk6_0,u1_struct_0(esk2_0))
        | ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
        | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
        | esk5_0 != k12_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( r1_orders_2(esk2_0,esk6_0,esk3_0)
        | ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
        | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
        | esk5_0 != k12_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( r1_orders_2(esk2_0,esk6_0,esk4_0)
        | ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
        | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
        | esk5_0 != k12_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( ~ r1_orders_2(esk2_0,esk6_0,esk5_0)
        | ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
        | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
        | esk5_0 != k12_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( r1_orders_2(esk2_0,esk5_0,esk3_0)
        | esk5_0 = k12_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( r1_orders_2(esk2_0,esk5_0,esk4_0)
        | esk5_0 = k12_lattice3(esk2_0,esk3_0,esk4_0) )
      & ( ~ m1_subset_1(X21,u1_struct_0(esk2_0))
        | ~ r1_orders_2(esk2_0,X21,esk3_0)
        | ~ r1_orders_2(esk2_0,X21,esk4_0)
        | r1_orders_2(esk2_0,X21,esk5_0)
        | esk5_0 = k12_lattice3(esk2_0,esk3_0,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_10,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ~ v5_orders_2(X13)
      | ~ v2_lattice3(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | k12_lattice3(X13,X14,X15) = k11_lattice3(X13,X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_12,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X4)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v2_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X1)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_10,c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk5_0)
    | esk5_0 = k12_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_0,esk4_0)
    | esk5_0 = k12_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_0,esk3_0)
    | esk5_0 = k12_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( k11_lattice3(esk2_0,X1,X2) = esk5_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,X2,esk5_0),X2)
    | ~ r1_orders_2(esk2_0,esk5_0,X2)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_25,negated_conjecture,
    ( k11_lattice3(esk2_0,X1,X2) = esk5_0
    | ~ r1_orders_2(esk2_0,esk1_4(esk2_0,X1,X2,esk5_0),esk5_0)
    | ~ r1_orders_2(esk2_0,esk5_0,X2)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_26,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk5_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_19]),c_0_20])).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,plain,
    ( r1_orders_2(X2,X1,X5)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X1,X4)
    | X5 != k11_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | ~ m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_21,c_0_8])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( k11_lattice3(esk2_0,X1,esk4_0) = k12_lattice3(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_32,negated_conjecture,
    ( k11_lattice3(esk2_0,X1,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk5_0,esk5_0),esk5_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k11_lattice3(esk2_0,X1,esk5_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk5_0,esk5_0),esk5_0)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_13])])).

cnf(c_0_34,negated_conjecture,
    ( k11_lattice3(esk2_0,X1,esk5_0) = k12_lattice3(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X2)
    | ~ m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_27,c_0_8])])).

cnf(c_0_36,plain,
    ( r1_orders_2(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(k11_lattice3(X1,X3,X4),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_28,c_0_8])])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk2_0,k11_lattice3(esk2_0,esk3_0,X1),X1)
    | ~ m1_subset_1(k11_lattice3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_38,negated_conjecture,
    ( k11_lattice3(esk2_0,esk3_0,esk4_0) = k12_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k11_lattice3(esk2_0,X1,esk5_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k11_lattice3(esk2_0,esk5_0,esk5_0) = k12_lattice3(esk2_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk2_0,k11_lattice3(esk2_0,X1,esk4_0),X1)
    | ~ m1_subset_1(k11_lattice3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_23]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_42,negated_conjecture,
    ( k11_lattice3(esk2_0,esk3_0,esk5_0) = k12_lattice3(esk2_0,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_43,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X2)
    | X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k11_lattice3(esk2_0,X2,esk4_0))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(k11_lattice3(esk2_0,X2,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk4_0)
    | ~ m1_subset_1(k12_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_23]),c_0_38]),c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk5_0) = esk5_0
    | k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_40]),c_0_13])])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk3_0)
    | ~ m1_subset_1(k12_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_38]),c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk5_0) = esk5_0
    | k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_42]),c_0_30])])).

cnf(c_0_49,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X3)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_43,c_0_8])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk2_0,k11_lattice3(esk2_0,esk5_0,X1),X1)
    | ~ m1_subset_1(k11_lattice3(esk2_0,esk5_0,X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k12_lattice3(esk2_0,esk3_0,esk4_0))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(k12_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_30]),c_0_38]),c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
    | esk5_0 != k12_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_53,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_13])])).

cnf(c_0_54,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_46]),c_0_13])])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk2_0,esk6_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
    | esk5_0 != k12_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk2_0,esk6_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
    | esk5_0 != k12_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk6_0,esk5_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
    | esk5_0 != k12_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_58,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_48]),c_0_13])])).

cnf(c_0_59,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_13])])).

cnf(c_0_60,negated_conjecture,
    ( k11_lattice3(esk2_0,X1,X2) = esk5_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,X2,esk5_0),X1)
    | ~ r1_orders_2(esk2_0,esk5_0,X2)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk2_0,k11_lattice3(esk2_0,esk5_0,esk5_0),esk5_0)
    | ~ m1_subset_1(k11_lattice3(esk2_0,esk5_0,esk5_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_13])).

cnf(c_0_62,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,X1,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_13])])).

cnf(c_0_63,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk5_0) = esk5_0
    | m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_53]),c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,esk6_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_46]),c_0_53]),c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,esk6_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_46]),c_0_53]),c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk5_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_46]),c_0_53]),c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk2_0,k11_lattice3(esk2_0,X1,esk5_0),X1)
    | ~ m1_subset_1(k11_lattice3(esk2_0,X1,esk5_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_68,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,X1,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_13])])).

cnf(c_0_69,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk5_0) = esk5_0
    | m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_58]),c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,esk6_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_58]),c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk5_0) = esk5_0
    | r1_orders_2(esk2_0,esk6_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_58]),c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk5_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_48]),c_0_58]),c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( k11_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),X1)
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk5_0,esk5_0),esk5_0)
    | ~ m1_subset_1(k12_lattice3(esk2_0,esk5_0,esk5_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_40]),c_0_40])).

cnf(c_0_75,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk5_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k11_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),esk5_0)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_23])])).

cnf(c_0_77,negated_conjecture,
    ( k11_lattice3(esk2_0,esk5_0,esk4_0) = k12_lattice3(esk2_0,esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_13])).

cnf(c_0_78,negated_conjecture,
    ( r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk3_0,esk5_0),esk3_0)
    | ~ m1_subset_1(k12_lattice3(esk2_0,esk3_0,esk5_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_30]),c_0_42]),c_0_42])).

cnf(c_0_79,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk5_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k11_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),X1)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_19])).

cnf(c_0_81,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_75]),c_0_13])])).

cnf(c_0_82,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk4_0) = esk5_0
    | k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk1_4(esk2_0,esk5_0,esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_26]),c_0_77]),c_0_13])])).

cnf(c_0_83,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))
    | X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_84,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_79]),c_0_13])])).

cnf(c_0_85,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk4_0) = esk5_0
    | k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_13]),c_0_77]),c_0_81])]),c_0_82])).

cnf(c_0_86,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | m1_subset_1(esk1_4(X2,X3,X4,X1),u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_83,c_0_8])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0))
    | k12_lattice3(esk2_0,esk3_0,esk4_0) != esk5_0
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_84])])).

cnf(c_0_88,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_85]),c_0_13])])).

cnf(c_0_89,negated_conjecture,
    ( r1_orders_2(esk2_0,esk6_0,esk3_0)
    | k12_lattice3(esk2_0,esk3_0,esk4_0) != esk5_0
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_84])])).

cnf(c_0_90,negated_conjecture,
    ( r1_orders_2(esk2_0,esk6_0,esk4_0)
    | k12_lattice3(esk2_0,esk3_0,esk4_0) != esk5_0
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_84])])).

cnf(c_0_91,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) != esk5_0
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_84])])).

cnf(c_0_92,negated_conjecture,
    ( k11_lattice3(esk2_0,X1,X2) = esk5_0
    | m1_subset_1(esk1_4(esk2_0,X1,X2,esk5_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,esk5_0,X2)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_93,negated_conjecture,
    ( k11_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk5_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_94,negated_conjecture,
    ( r1_orders_2(esk2_0,k11_lattice3(esk2_0,esk5_0,esk4_0),esk4_0)
    | ~ m1_subset_1(k11_lattice3(esk2_0,esk5_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_23])).

cnf(c_0_95,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,X1,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_85]),c_0_13])])).

cnf(c_0_96,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk4_0) = esk5_0
    | m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_85]),c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk6_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_85]),c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk6_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_85]),c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk4_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_85]),c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k11_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | m1_subset_1(esk1_4(esk2_0,X1,esk4_0,esk5_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_19]),c_0_23])])).

cnf(c_0_101,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | k11_lattice3(esk2_0,X1,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_19])).

cnf(c_0_102,negated_conjecture,
    ( r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk5_0,esk4_0),esk4_0)
    | ~ m1_subset_1(k12_lattice3(esk2_0,esk5_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_77]),c_0_77])).

cnf(c_0_103,negated_conjecture,
    ( k12_lattice3(esk2_0,esk5_0,esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),c_0_98]),c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | m1_subset_1(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_20]),c_0_38]),c_0_30])])).

cnf(c_0_105,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_30]),c_0_38])]),c_0_20])).

cnf(c_0_106,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | r1_orders_2(esk2_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_30]),c_0_38])]),c_0_20])).

cnf(c_0_107,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0
    | ~ r1_orders_2(esk2_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_20]),c_0_38]),c_0_30])])).

cnf(c_0_108,negated_conjecture,
    ( r1_orders_2(esk2_0,esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_103]),c_0_13])])).

cnf(c_0_109,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_104]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0))
    | k12_lattice3(esk2_0,esk3_0,esk4_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_108])])).

cnf(c_0_111,negated_conjecture,
    ( r1_orders_2(esk2_0,esk6_0,esk4_0)
    | k12_lattice3(esk2_0,esk3_0,esk4_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_108])])).

cnf(c_0_112,negated_conjecture,
    ( r1_orders_2(esk2_0,esk6_0,esk3_0)
    | k12_lattice3(esk2_0,esk3_0,esk4_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_108])])).

cnf(c_0_113,negated_conjecture,
    ( k12_lattice3(esk2_0,esk3_0,esk4_0) != esk5_0
    | ~ r1_orders_2(esk2_0,esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_108])])).

cnf(c_0_114,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_109]),c_0_109]),c_0_13])])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_109])])).

cnf(c_0_116,negated_conjecture,
    ( r1_orders_2(esk2_0,esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_109])])).

cnf(c_0_117,negated_conjecture,
    ( r1_orders_2(esk2_0,esk6_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_109])])).

cnf(c_0_118,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_109])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116]),c_0_117])]),c_0_118]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.13/0.41  # and selection function SelectNewComplexAHP.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.027 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 0.13/0.41  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.13/0.41  fof(t23_yellow_0, conjecture, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k12_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_0)).
% 0.13/0.41  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.13/0.41  fof(c_0_4, plain, ![X7, X8, X9, X10, X11]:((((r1_orders_2(X7,X10,X8)|X10!=k11_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v2_lattice3(X7)|~l1_orders_2(X7)))&(r1_orders_2(X7,X10,X9)|X10!=k11_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v2_lattice3(X7)|~l1_orders_2(X7))))&(~m1_subset_1(X11,u1_struct_0(X7))|(~r1_orders_2(X7,X11,X8)|~r1_orders_2(X7,X11,X9)|r1_orders_2(X7,X11,X10))|X10!=k11_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v2_lattice3(X7)|~l1_orders_2(X7))))&((m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))|(~r1_orders_2(X7,X10,X8)|~r1_orders_2(X7,X10,X9))|X10=k11_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v2_lattice3(X7)|~l1_orders_2(X7)))&(((r1_orders_2(X7,esk1_4(X7,X8,X9,X10),X8)|(~r1_orders_2(X7,X10,X8)|~r1_orders_2(X7,X10,X9))|X10=k11_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v2_lattice3(X7)|~l1_orders_2(X7)))&(r1_orders_2(X7,esk1_4(X7,X8,X9,X10),X9)|(~r1_orders_2(X7,X10,X8)|~r1_orders_2(X7,X10,X9))|X10=k11_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v2_lattice3(X7)|~l1_orders_2(X7))))&(~r1_orders_2(X7,esk1_4(X7,X8,X9,X10),X10)|(~r1_orders_2(X7,X10,X8)|~r1_orders_2(X7,X10,X9))|X10=k11_lattice3(X7,X8,X9)|~m1_subset_1(X10,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v5_orders_2(X7)|~v2_lattice3(X7)|~l1_orders_2(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.13/0.41  fof(c_0_5, plain, ![X6]:(~l1_orders_2(X6)|(~v2_lattice3(X6)|~v2_struct_0(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.13/0.41  fof(c_0_6, negated_conjecture, ~(![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k12_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4)))))))))), inference(assume_negation,[status(cth)],[t23_yellow_0])).
% 0.13/0.41  cnf(c_0_7, plain, (r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X3)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.41  cnf(c_0_8, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.41  fof(c_0_9, negated_conjecture, ![X21]:(((v5_orders_2(esk2_0)&v2_lattice3(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(esk2_0))&(((m1_subset_1(esk6_0,u1_struct_0(esk2_0))|(~r1_orders_2(esk2_0,esk5_0,esk3_0)|~r1_orders_2(esk2_0,esk5_0,esk4_0))|esk5_0!=k12_lattice3(esk2_0,esk3_0,esk4_0))&(((r1_orders_2(esk2_0,esk6_0,esk3_0)|(~r1_orders_2(esk2_0,esk5_0,esk3_0)|~r1_orders_2(esk2_0,esk5_0,esk4_0))|esk5_0!=k12_lattice3(esk2_0,esk3_0,esk4_0))&(r1_orders_2(esk2_0,esk6_0,esk4_0)|(~r1_orders_2(esk2_0,esk5_0,esk3_0)|~r1_orders_2(esk2_0,esk5_0,esk4_0))|esk5_0!=k12_lattice3(esk2_0,esk3_0,esk4_0)))&(~r1_orders_2(esk2_0,esk6_0,esk5_0)|(~r1_orders_2(esk2_0,esk5_0,esk3_0)|~r1_orders_2(esk2_0,esk5_0,esk4_0))|esk5_0!=k12_lattice3(esk2_0,esk3_0,esk4_0))))&(((r1_orders_2(esk2_0,esk5_0,esk3_0)|esk5_0=k12_lattice3(esk2_0,esk3_0,esk4_0))&(r1_orders_2(esk2_0,esk5_0,esk4_0)|esk5_0=k12_lattice3(esk2_0,esk3_0,esk4_0)))&(~m1_subset_1(X21,u1_struct_0(esk2_0))|(~r1_orders_2(esk2_0,X21,esk3_0)|~r1_orders_2(esk2_0,X21,esk4_0)|r1_orders_2(esk2_0,X21,esk5_0))|esk5_0=k12_lattice3(esk2_0,esk3_0,esk4_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.13/0.41  cnf(c_0_10, plain, (X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.41  fof(c_0_11, plain, ![X13, X14, X15]:(~v5_orders_2(X13)|~v2_lattice3(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))|k12_lattice3(X13,X14,X15)=k11_lattice3(X13,X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.13/0.41  cnf(c_0_12, plain, (X1=k11_lattice3(X2,X3,X4)|r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X4)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_7, c_0_8])).
% 0.13/0.41  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_14, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_15, negated_conjecture, (v2_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_17, plain, (X1=k11_lattice3(X2,X3,X4)|~r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X1)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_10, c_0_8])).
% 0.13/0.41  cnf(c_0_18, negated_conjecture, (r1_orders_2(esk2_0,X1,esk5_0)|esk5_0=k12_lattice3(esk2_0,esk3_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,esk3_0)|~r1_orders_2(esk2_0,X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_19, negated_conjecture, (r1_orders_2(esk2_0,esk5_0,esk4_0)|esk5_0=k12_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_20, negated_conjecture, (r1_orders_2(esk2_0,esk5_0,esk3_0)|esk5_0=k12_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_21, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.41  cnf(c_0_22, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_24, negated_conjecture, (k11_lattice3(esk2_0,X1,X2)=esk5_0|r1_orders_2(esk2_0,esk1_4(esk2_0,X1,X2,esk5_0),X2)|~r1_orders_2(esk2_0,esk5_0,X2)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_25, negated_conjecture, (k11_lattice3(esk2_0,X1,X2)=esk5_0|~r1_orders_2(esk2_0,esk1_4(esk2_0,X1,X2,esk5_0),esk5_0)|~r1_orders_2(esk2_0,esk5_0,X2)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_26, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk5_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_13]), c_0_19]), c_0_20])).
% 0.13/0.41  cnf(c_0_27, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X2!=k11_lattice3(X1,X3,X4)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.41  cnf(c_0_28, plain, (r1_orders_2(X2,X1,X5)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,X1,X3)|~r1_orders_2(X2,X1,X4)|X5!=k11_lattice3(X2,X3,X4)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.41  cnf(c_0_29, plain, (r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)|~m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_21, c_0_8])])).
% 0.13/0.41  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_31, negated_conjecture, (k11_lattice3(esk2_0,X1,esk4_0)=k12_lattice3(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_32, negated_conjecture, (k11_lattice3(esk2_0,X1,esk5_0)=esk5_0|r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk5_0,esk5_0),esk5_0)|~r1_orders_2(esk2_0,esk5_0,esk5_0)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_24, c_0_13])).
% 0.13/0.41  cnf(c_0_33, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k11_lattice3(esk2_0,X1,esk5_0)=esk5_0|~r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk5_0,esk5_0),esk5_0)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_13])])).
% 0.13/0.41  cnf(c_0_34, negated_conjecture, (k11_lattice3(esk2_0,X1,esk5_0)=k12_lattice3(esk2_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_13]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_35, plain, (r1_orders_2(X1,k11_lattice3(X1,X2,X3),X2)|~m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_27, c_0_8])])).
% 0.13/0.41  cnf(c_0_36, plain, (r1_orders_2(X1,X2,k11_lattice3(X1,X3,X4))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(k11_lattice3(X1,X3,X4),u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_28, c_0_8])])).
% 0.13/0.41  cnf(c_0_37, negated_conjecture, (r1_orders_2(esk2_0,k11_lattice3(esk2_0,esk3_0,X1),X1)|~m1_subset_1(k11_lattice3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (k11_lattice3(esk2_0,esk3_0,esk4_0)=k12_lattice3(esk2_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.13/0.41  cnf(c_0_39, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k11_lattice3(esk2_0,X1,esk5_0)=esk5_0|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_33])).
% 0.13/0.41  cnf(c_0_40, negated_conjecture, (k11_lattice3(esk2_0,esk5_0,esk5_0)=k12_lattice3(esk2_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_13])).
% 0.13/0.41  cnf(c_0_41, negated_conjecture, (r1_orders_2(esk2_0,k11_lattice3(esk2_0,X1,esk4_0),X1)|~m1_subset_1(k11_lattice3(esk2_0,X1,esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_23]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_42, negated_conjecture, (k11_lattice3(esk2_0,esk3_0,esk5_0)=k12_lattice3(esk2_0,esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_30])).
% 0.13/0.41  cnf(c_0_43, plain, (r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X2)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.41  cnf(c_0_44, negated_conjecture, (r1_orders_2(esk2_0,X1,k11_lattice3(esk2_0,X2,esk4_0))|~r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(k11_lattice3(esk2_0,X2,esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_23]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk4_0)|~m1_subset_1(k12_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_23]), c_0_38]), c_0_38])).
% 0.13/0.41  cnf(c_0_46, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk5_0)=esk5_0|k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_40]), c_0_13])])).
% 0.13/0.41  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk3_0,esk4_0),esk3_0)|~m1_subset_1(k12_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30]), c_0_38]), c_0_38])).
% 0.13/0.41  cnf(c_0_48, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk5_0)=esk5_0|k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_42]), c_0_30])])).
% 0.13/0.41  cnf(c_0_49, plain, (X1=k11_lattice3(X2,X3,X4)|r1_orders_2(X2,esk1_4(X2,X3,X4,X1),X3)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_43, c_0_8])).
% 0.13/0.41  cnf(c_0_50, negated_conjecture, (r1_orders_2(esk2_0,k11_lattice3(esk2_0,esk5_0,X1),X1)|~m1_subset_1(k11_lattice3(esk2_0,esk5_0,X1),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_13]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk2_0,X1,k12_lattice3(esk2_0,esk3_0,esk4_0))|~r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(k12_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_30]), c_0_38]), c_0_38])).
% 0.13/0.41  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,esk5_0,esk3_0)|~r1_orders_2(esk2_0,esk5_0,esk4_0)|esk5_0!=k12_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_53, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_13])])).
% 0.13/0.41  cnf(c_0_54, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_46]), c_0_13])])).
% 0.13/0.41  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk2_0,esk6_0,esk3_0)|~r1_orders_2(esk2_0,esk5_0,esk3_0)|~r1_orders_2(esk2_0,esk5_0,esk4_0)|esk5_0!=k12_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk2_0,esk6_0,esk4_0)|~r1_orders_2(esk2_0,esk5_0,esk3_0)|~r1_orders_2(esk2_0,esk5_0,esk4_0)|esk5_0!=k12_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_57, negated_conjecture, (~r1_orders_2(esk2_0,esk6_0,esk5_0)|~r1_orders_2(esk2_0,esk5_0,esk3_0)|~r1_orders_2(esk2_0,esk5_0,esk4_0)|esk5_0!=k12_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_58, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_48]), c_0_13])])).
% 0.13/0.41  cnf(c_0_59, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_13])])).
% 0.13/0.41  cnf(c_0_60, negated_conjecture, (k11_lattice3(esk2_0,X1,X2)=esk5_0|r1_orders_2(esk2_0,esk1_4(esk2_0,X1,X2,esk5_0),X1)|~r1_orders_2(esk2_0,esk5_0,X2)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_13]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk2_0,k11_lattice3(esk2_0,esk5_0,esk5_0),esk5_0)|~m1_subset_1(k11_lattice3(esk2_0,esk5_0,esk5_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_13])).
% 0.13/0.41  cnf(c_0_62, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,X1,esk5_0)|~r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_46]), c_0_13])])).
% 0.13/0.41  cnf(c_0_63, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk5_0)=esk5_0|m1_subset_1(esk6_0,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_46]), c_0_53]), c_0_54])).
% 0.13/0.41  cnf(c_0_64, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,esk6_0,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_46]), c_0_53]), c_0_54])).
% 0.13/0.41  cnf(c_0_65, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,esk6_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_46]), c_0_53]), c_0_54])).
% 0.13/0.41  cnf(c_0_66, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk5_0)=esk5_0|~r1_orders_2(esk2_0,esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_46]), c_0_53]), c_0_54])).
% 0.13/0.41  cnf(c_0_67, negated_conjecture, (r1_orders_2(esk2_0,k11_lattice3(esk2_0,X1,esk5_0),X1)|~m1_subset_1(k11_lattice3(esk2_0,X1,esk5_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_13]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_68, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,X1,esk5_0)|~r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_13])])).
% 0.13/0.41  cnf(c_0_69, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk5_0)=esk5_0|m1_subset_1(esk6_0,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_58]), c_0_59])).
% 0.13/0.41  cnf(c_0_70, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,esk6_0,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_48]), c_0_58]), c_0_59])).
% 0.13/0.41  cnf(c_0_71, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk5_0)=esk5_0|r1_orders_2(esk2_0,esk6_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_48]), c_0_58]), c_0_59])).
% 0.13/0.41  cnf(c_0_72, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk5_0)=esk5_0|~r1_orders_2(esk2_0,esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_48]), c_0_58]), c_0_59])).
% 0.13/0.41  cnf(c_0_73, negated_conjecture, (k11_lattice3(esk2_0,X1,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),X1)|~r1_orders_2(esk2_0,esk5_0,esk4_0)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_23])).
% 0.13/0.41  cnf(c_0_74, negated_conjecture, (r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk5_0,esk5_0),esk5_0)|~m1_subset_1(k12_lattice3(esk2_0,esk5_0,esk5_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_40]), c_0_40])).
% 0.13/0.41  cnf(c_0_75, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk5_0)=esk5_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), c_0_66])).
% 0.13/0.41  cnf(c_0_76, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k11_lattice3(esk2_0,X1,esk4_0)=esk5_0|~r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),esk5_0)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_19]), c_0_23])])).
% 0.13/0.41  cnf(c_0_77, negated_conjecture, (k11_lattice3(esk2_0,esk5_0,esk4_0)=k12_lattice3(esk2_0,esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_13])).
% 0.13/0.41  cnf(c_0_78, negated_conjecture, (r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk3_0,esk5_0),esk3_0)|~m1_subset_1(k12_lattice3(esk2_0,esk3_0,esk5_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_30]), c_0_42]), c_0_42])).
% 0.13/0.41  cnf(c_0_79, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk5_0)=esk5_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71]), c_0_72])).
% 0.13/0.41  cnf(c_0_80, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k11_lattice3(esk2_0,X1,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),X1)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_73, c_0_19])).
% 0.13/0.41  cnf(c_0_81, negated_conjecture, (r1_orders_2(esk2_0,esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_75]), c_0_13])])).
% 0.13/0.41  cnf(c_0_82, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk4_0)=esk5_0|k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|~r1_orders_2(esk2_0,esk1_4(esk2_0,esk5_0,esk4_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_26]), c_0_77]), c_0_13])])).
% 0.13/0.41  cnf(c_0_83, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.41  cnf(c_0_84, negated_conjecture, (r1_orders_2(esk2_0,esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79]), c_0_79]), c_0_13])])).
% 0.13/0.41  cnf(c_0_85, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk4_0)=esk5_0|k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_13]), c_0_77]), c_0_81])]), c_0_82])).
% 0.13/0.41  cnf(c_0_86, plain, (X1=k11_lattice3(X2,X3,X4)|m1_subset_1(esk1_4(X2,X3,X4,X1),u1_struct_0(X2))|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_83, c_0_8])).
% 0.13/0.41  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))|k12_lattice3(esk2_0,esk3_0,esk4_0)!=esk5_0|~r1_orders_2(esk2_0,esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_84])])).
% 0.13/0.41  cnf(c_0_88, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_85]), c_0_13])])).
% 0.13/0.41  cnf(c_0_89, negated_conjecture, (r1_orders_2(esk2_0,esk6_0,esk3_0)|k12_lattice3(esk2_0,esk3_0,esk4_0)!=esk5_0|~r1_orders_2(esk2_0,esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_84])])).
% 0.13/0.41  cnf(c_0_90, negated_conjecture, (r1_orders_2(esk2_0,esk6_0,esk4_0)|k12_lattice3(esk2_0,esk3_0,esk4_0)!=esk5_0|~r1_orders_2(esk2_0,esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_84])])).
% 0.13/0.41  cnf(c_0_91, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)!=esk5_0|~r1_orders_2(esk2_0,esk5_0,esk4_0)|~r1_orders_2(esk2_0,esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_84])])).
% 0.13/0.41  cnf(c_0_92, negated_conjecture, (k11_lattice3(esk2_0,X1,X2)=esk5_0|m1_subset_1(esk1_4(esk2_0,X1,X2,esk5_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,esk5_0,X2)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_13]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.41  cnf(c_0_93, negated_conjecture, (k11_lattice3(esk2_0,X1,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),esk4_0)|~r1_orders_2(esk2_0,esk5_0,esk4_0)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.13/0.41  cnf(c_0_94, negated_conjecture, (r1_orders_2(esk2_0,k11_lattice3(esk2_0,esk5_0,esk4_0),esk4_0)|~m1_subset_1(k11_lattice3(esk2_0,esk5_0,esk4_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_23])).
% 0.13/0.41  cnf(c_0_95, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk4_0)=esk5_0|r1_orders_2(esk2_0,X1,esk5_0)|~r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_85]), c_0_13])])).
% 0.13/0.41  cnf(c_0_96, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk4_0)=esk5_0|m1_subset_1(esk6_0,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_85]), c_0_88])).
% 0.13/0.41  cnf(c_0_97, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk6_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_85]), c_0_88])).
% 0.13/0.41  cnf(c_0_98, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk6_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_85]), c_0_88])).
% 0.13/0.41  cnf(c_0_99, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk4_0)=esk5_0|~r1_orders_2(esk2_0,esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_85]), c_0_88])).
% 0.13/0.41  cnf(c_0_100, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k11_lattice3(esk2_0,X1,esk4_0)=esk5_0|m1_subset_1(esk1_4(esk2_0,X1,esk4_0,esk5_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_19]), c_0_23])])).
% 0.13/0.41  cnf(c_0_101, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|k11_lattice3(esk2_0,X1,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk1_4(esk2_0,X1,esk4_0,esk5_0),esk4_0)|~r1_orders_2(esk2_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_93, c_0_19])).
% 0.13/0.41  cnf(c_0_102, negated_conjecture, (r1_orders_2(esk2_0,k12_lattice3(esk2_0,esk5_0,esk4_0),esk4_0)|~m1_subset_1(k12_lattice3(esk2_0,esk5_0,esk4_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_77]), c_0_77])).
% 0.13/0.41  cnf(c_0_103, negated_conjecture, (k12_lattice3(esk2_0,esk5_0,esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97]), c_0_98]), c_0_99])).
% 0.13/0.41  cnf(c_0_104, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|m1_subset_1(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_20]), c_0_38]), c_0_30])])).
% 0.13/0.41  cnf(c_0_105, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_30]), c_0_38])]), c_0_20])).
% 0.13/0.41  cnf(c_0_106, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|r1_orders_2(esk2_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_30]), c_0_38])]), c_0_20])).
% 0.13/0.41  cnf(c_0_107, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0|~r1_orders_2(esk2_0,esk1_4(esk2_0,esk3_0,esk4_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_20]), c_0_38]), c_0_30])])).
% 0.13/0.41  cnf(c_0_108, negated_conjecture, (r1_orders_2(esk2_0,esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_103]), c_0_13])])).
% 0.13/0.41  cnf(c_0_109, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_104]), c_0_105]), c_0_106]), c_0_107])).
% 0.13/0.41  cnf(c_0_110, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))|k12_lattice3(esk2_0,esk3_0,esk4_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_108])])).
% 0.13/0.41  cnf(c_0_111, negated_conjecture, (r1_orders_2(esk2_0,esk6_0,esk4_0)|k12_lattice3(esk2_0,esk3_0,esk4_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_108])])).
% 0.13/0.41  cnf(c_0_112, negated_conjecture, (r1_orders_2(esk2_0,esk6_0,esk3_0)|k12_lattice3(esk2_0,esk3_0,esk4_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_108])])).
% 0.13/0.41  cnf(c_0_113, negated_conjecture, (k12_lattice3(esk2_0,esk3_0,esk4_0)!=esk5_0|~r1_orders_2(esk2_0,esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_108])])).
% 0.13/0.41  cnf(c_0_114, negated_conjecture, (r1_orders_2(esk2_0,X1,esk5_0)|~r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_109]), c_0_109]), c_0_13])])).
% 0.13/0.41  cnf(c_0_115, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_109])])).
% 0.13/0.41  cnf(c_0_116, negated_conjecture, (r1_orders_2(esk2_0,esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_109])])).
% 0.13/0.41  cnf(c_0_117, negated_conjecture, (r1_orders_2(esk2_0,esk6_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_109])])).
% 0.13/0.41  cnf(c_0_118, negated_conjecture, (~r1_orders_2(esk2_0,esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_109])])).
% 0.13/0.41  cnf(c_0_119, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_116]), c_0_117])]), c_0_118]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 120
% 0.13/0.41  # Proof object clause steps            : 111
% 0.13/0.41  # Proof object formula steps           : 9
% 0.13/0.41  # Proof object conjectures             : 98
% 0.13/0.41  # Proof object clause conjectures      : 95
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 22
% 0.13/0.41  # Proof object initial formulas used   : 4
% 0.13/0.41  # Proof object generating inferences   : 64
% 0.13/0.41  # Proof object simplifying inferences  : 192
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 4
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 22
% 0.13/0.41  # Removed in clause preprocessing      : 0
% 0.13/0.41  # Initial clauses in saturation        : 22
% 0.13/0.41  # Processed clauses                    : 347
% 0.13/0.41  # ...of these trivial                  : 2
% 0.13/0.41  # ...subsumed                          : 37
% 0.13/0.41  # ...remaining for further processing  : 308
% 0.13/0.41  # Other redundant clauses eliminated   : 3
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 60
% 0.13/0.41  # Backward-rewritten                   : 119
% 0.13/0.41  # Generated clauses                    : 887
% 0.13/0.41  # ...of the previous two non-trivial   : 897
% 0.13/0.41  # Contextual simplify-reflections      : 55
% 0.13/0.41  # Paramodulations                      : 884
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 3
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 104
% 0.13/0.41  #    Positive orientable unit clauses  : 32
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 1
% 0.13/0.41  #    Non-unit-clauses                  : 71
% 0.13/0.41  # Current number of unprocessed clauses: 420
% 0.13/0.41  # ...number of literals in the above   : 2073
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 201
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 2936
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 680
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 148
% 0.13/0.41  # Unit Clause-clause subsumption calls : 619
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 95
% 0.13/0.41  # BW rewrite match successes           : 15
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 32301
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.061 s
% 0.13/0.41  # System time              : 0.007 s
% 0.13/0.41  # Total time               : 0.068 s
% 0.13/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
