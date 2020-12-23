%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1542+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 17.40s
% Output     : CNFRefutation 17.40s
% Verified   : 
% Statistics : Number of formulae       :   94 (19233 expanded)
%              Number of clauses        :   79 (7369 expanded)
%              Number of leaves         :    6 (4705 expanded)
%              Depth                    :   19
%              Number of atoms          :  553 (193639 expanded)
%              Number of equality atoms :   19 (3663 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   66 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_yellow_0,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_0)).

fof(d10_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                    & r1_orders_2(X1,X2,X4)
                    & r1_orders_2(X1,X3,X4)
                    & ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( ( r1_orders_2(X1,X2,X5)
                            & r1_orders_2(X1,X3,X5) )
                         => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_lattice3)).

fof(t18_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( ( X4 = k10_lattice3(X1,X2,X3)
                        & r1_yellow_0(X1,k2_tarski(X2,X3)) )
                     => ( r1_orders_2(X1,X2,X4)
                        & r1_orders_2(X1,X3,X4)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_orders_2(X1,X2,X5)
                                & r1_orders_2(X1,X3,X5) )
                             => r1_orders_2(X1,X4,X5) ) ) ) )
                    & ( ( r1_orders_2(X1,X2,X4)
                        & r1_orders_2(X1,X3,X4)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_orders_2(X1,X2,X5)
                                & r1_orders_2(X1,X3,X5) )
                             => r1_orders_2(X1,X4,X5) ) ) )
                     => ( X4 = k10_lattice3(X1,X2,X3)
                        & r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_0)).

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_5,plain,(
    ! [X2,X1,X3] :
      ( epred1_3(X3,X1,X2)
    <=> ! [X4] :
          ( m1_subset_1(X4,u1_struct_0(X1))
         => ( ( ( X4 = k10_lattice3(X1,X2,X3)
                & r1_yellow_0(X1,k2_tarski(X2,X3)) )
             => ( r1_orders_2(X1,X2,X4)
                & r1_orders_2(X1,X3,X4)
                & ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X5)
                        & r1_orders_2(X1,X3,X5) )
                     => r1_orders_2(X1,X4,X5) ) ) ) )
            & ( ( r1_orders_2(X1,X2,X4)
                & r1_orders_2(X1,X3,X4)
                & ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X5)
                        & r1_orders_2(X1,X3,X5) )
                     => r1_orders_2(X1,X4,X5) ) ) )
             => ( X4 = k10_lattice3(X1,X2,X3)
                & r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ) ),
    introduced(definition)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ( v1_lattice3(X1)
        <=> ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_yellow_0])).

fof(c_0_7,plain,(
    ! [X2,X1,X3] :
      ( epred1_3(X3,X1,X2)
     => ! [X4] :
          ( m1_subset_1(X4,u1_struct_0(X1))
         => ( ( ( X4 = k10_lattice3(X1,X2,X3)
                & r1_yellow_0(X1,k2_tarski(X2,X3)) )
             => ( r1_orders_2(X1,X2,X4)
                & r1_orders_2(X1,X3,X4)
                & ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X5)
                        & r1_orders_2(X1,X3,X5) )
                     => r1_orders_2(X1,X4,X5) ) ) ) )
            & ( ( r1_orders_2(X1,X2,X4)
                & r1_orders_2(X1,X3,X4)
                & ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X5)
                        & r1_orders_2(X1,X3,X5) )
                     => r1_orders_2(X1,X4,X5) ) ) )
             => ( X4 = k10_lattice3(X1,X2,X3)
                & r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X12,X15] :
      ( ( m1_subset_1(esk1_3(X8,X9,X10),u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v1_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( r1_orders_2(X8,X9,esk1_3(X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v1_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( r1_orders_2(X8,X10,esk1_3(X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v1_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ m1_subset_1(X12,u1_struct_0(X8))
        | ~ r1_orders_2(X8,X9,X12)
        | ~ r1_orders_2(X8,X10,X12)
        | r1_orders_2(X8,esk1_3(X8,X9,X10),X12)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v1_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk2_1(X8),u1_struct_0(X8))
        | v1_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk3_1(X8),u1_struct_0(X8))
        | v1_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk4_2(X8,X15),u1_struct_0(X8))
        | ~ m1_subset_1(X15,u1_struct_0(X8))
        | ~ r1_orders_2(X8,esk2_1(X8),X15)
        | ~ r1_orders_2(X8,esk3_1(X8),X15)
        | v1_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( r1_orders_2(X8,esk2_1(X8),esk4_2(X8,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X8))
        | ~ r1_orders_2(X8,esk2_1(X8),X15)
        | ~ r1_orders_2(X8,esk3_1(X8),X15)
        | v1_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( r1_orders_2(X8,esk3_1(X8),esk4_2(X8,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X8))
        | ~ r1_orders_2(X8,esk2_1(X8),X15)
        | ~ r1_orders_2(X8,esk3_1(X8),X15)
        | v1_lattice3(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ r1_orders_2(X8,X15,esk4_2(X8,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X8))
        | ~ r1_orders_2(X8,esk2_1(X8),X15)
        | ~ r1_orders_2(X8,esk3_1(X8),X15)
        | v1_lattice3(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_lattice3])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X26,X27] :
      ( v5_orders_2(esk5_0)
      & l1_orders_2(esk5_0)
      & ( m1_subset_1(esk6_0,u1_struct_0(esk5_0))
        | ~ v1_lattice3(esk5_0) )
      & ( m1_subset_1(esk7_0,u1_struct_0(esk5_0))
        | ~ v1_lattice3(esk5_0) )
      & ( ~ r1_yellow_0(esk5_0,k2_tarski(esk6_0,esk7_0))
        | ~ v1_lattice3(esk5_0) )
      & ( v1_lattice3(esk5_0)
        | ~ m1_subset_1(X26,u1_struct_0(esk5_0))
        | ~ m1_subset_1(X27,u1_struct_0(esk5_0))
        | r1_yellow_0(esk5_0,k2_tarski(X26,X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_10,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => epred1_3(X3,X1,X2) ) ) ) ),
    inference(apply_def,[status(thm)],[t18_yellow_0,c_0_5])).

fof(c_0_11,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( ( r1_orders_2(X29,X28,X31)
        | X31 != k10_lattice3(X29,X28,X30)
        | ~ r1_yellow_0(X29,k2_tarski(X28,X30))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( r1_orders_2(X29,X30,X31)
        | X31 != k10_lattice3(X29,X28,X30)
        | ~ r1_yellow_0(X29,k2_tarski(X28,X30))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ r1_orders_2(X29,X28,X32)
        | ~ r1_orders_2(X29,X30,X32)
        | r1_orders_2(X29,X31,X32)
        | X31 != k10_lattice3(X29,X28,X30)
        | ~ r1_yellow_0(X29,k2_tarski(X28,X30))
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( X31 = k10_lattice3(X29,X28,X30)
        | m1_subset_1(esk8_4(X28,X29,X30,X31),u1_struct_0(X29))
        | ~ r1_orders_2(X29,X28,X31)
        | ~ r1_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( r1_yellow_0(X29,k2_tarski(X28,X30))
        | m1_subset_1(esk8_4(X28,X29,X30,X31),u1_struct_0(X29))
        | ~ r1_orders_2(X29,X28,X31)
        | ~ r1_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( X31 = k10_lattice3(X29,X28,X30)
        | r1_orders_2(X29,X28,esk8_4(X28,X29,X30,X31))
        | ~ r1_orders_2(X29,X28,X31)
        | ~ r1_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( r1_yellow_0(X29,k2_tarski(X28,X30))
        | r1_orders_2(X29,X28,esk8_4(X28,X29,X30,X31))
        | ~ r1_orders_2(X29,X28,X31)
        | ~ r1_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( X31 = k10_lattice3(X29,X28,X30)
        | r1_orders_2(X29,X30,esk8_4(X28,X29,X30,X31))
        | ~ r1_orders_2(X29,X28,X31)
        | ~ r1_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( r1_yellow_0(X29,k2_tarski(X28,X30))
        | r1_orders_2(X29,X30,esk8_4(X28,X29,X30,X31))
        | ~ r1_orders_2(X29,X28,X31)
        | ~ r1_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( X31 = k10_lattice3(X29,X28,X30)
        | ~ r1_orders_2(X29,X31,esk8_4(X28,X29,X30,X31))
        | ~ r1_orders_2(X29,X28,X31)
        | ~ r1_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) )
      & ( r1_yellow_0(X29,k2_tarski(X28,X30))
        | ~ r1_orders_2(X29,X31,esk8_4(X28,X29,X30,X31))
        | ~ r1_orders_2(X29,X28,X31)
        | ~ r1_orders_2(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ epred1_3(X30,X29,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X20,X21,X22] :
      ( ~ v5_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | epred1_3(X22,X20,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X4,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | m1_subset_1(k10_lattice3(X17,X18,X19),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

cnf(c_0_18,negated_conjecture,
    ( v1_lattice3(esk5_0)
    | r1_yellow_0(esk5_0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_1(esk5_0),u1_struct_0(esk5_0))
    | v1_lattice3(esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_20,plain,(
    ! [X6,X7] : k2_tarski(X6,X7) = k2_tarski(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_21,plain,
    ( epred1_3(X3,X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_1(esk5_0),u1_struct_0(esk5_0))
    | v1_lattice3(esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X4,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X2,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(X1,esk2_1(esk5_0)))
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( epred1_3(esk3_1(esk5_0),esk5_0,X1)
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_13])])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ epred1_3(X2,X1,X3)
    | ~ r1_yellow_0(X1,k2_tarski(X3,X2))
    | ~ m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_orders_2(X2,X5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k10_lattice3(X2,X3,X4)
    | ~ r1_yellow_0(X2,k2_tarski(X3,X4))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(esk2_1(esk5_0),esk3_1(esk5_0)))
    | v1_lattice3(esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( epred1_3(esk3_1(esk5_0),esk5_0,esk2_1(esk5_0))
    | v1_lattice3(esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ epred1_3(X2,X1,X3)
    | ~ r1_yellow_0(X1,k2_tarski(X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_36,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_orders_2(X1,esk3_1(X1),esk4_2(X1,X2))
    | v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk2_1(X1),X2)
    | ~ r1_orders_2(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk5_0,esk2_1(esk5_0),k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0)))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_13])]),c_0_19]),c_0_22]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk5_0,esk3_1(esk5_0),k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0)))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_13])]),c_0_19]),c_0_22]),c_0_34])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk2_1(X1),X2)
    | ~ r1_orders_2(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,plain,
    ( r1_orders_2(X1,esk2_1(X1),esk4_2(X1,X2))
    | v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk2_1(X1),X2)
    | ~ r1_orders_2(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk8_4(X2,X1,X3,X4),u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_44,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk5_0,esk3_1(esk5_0),esk4_2(esk5_0,k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0))))
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_13])]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0))),u1_struct_0(esk5_0))
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_13])]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk5_0,esk2_1(esk5_0),esk4_2(esk5_0,k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0))))
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_13])]),c_0_39])).

cnf(c_0_48,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk8_4(X2,X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk8_4(X2,X1,X3,esk1_3(X1,X4,X5)),u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X3,esk1_3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk5_0,k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0)),X1)
    | v1_lattice3(esk5_0)
    | ~ r1_orders_2(esk5_0,esk3_1(esk5_0),X1)
    | ~ r1_orders_2(esk5_0,esk2_1(esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_33]),c_0_13])]),c_0_19]),c_0_22]),c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk5_0,esk3_1(esk5_0),esk4_2(esk5_0,k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0))))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_13])]),c_0_19]),c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0))),u1_struct_0(esk5_0))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_26]),c_0_13])]),c_0_19]),c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk5_0,esk2_1(esk5_0),esk4_2(esk5_0,k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0))))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_26]),c_0_13])]),c_0_19]),c_0_22])).

cnf(c_0_55,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk8_4(X2,X1,X3,esk1_3(X1,X4,X5)))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X3,esk1_3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_56,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk8_4(X2,X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk8_4(X2,X1,X3,esk1_3(X1,X4,X3)),u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X4,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_60,plain,
    ( v1_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk4_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk2_1(X1),X2)
    | ~ r1_orders_2(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk5_0,k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0)),esk4_2(esk5_0,k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0))))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_62,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk8_4(X2,X1,X3,esk1_3(X1,X4,X3)))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X4,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_63,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk8_4(X2,X1,X3,esk1_3(X1,X4,X5)))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X3,esk1_3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_43])).

cnf(c_0_64,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk8_4(X2,X1,X3,esk1_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( epred1_3(esk6_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_59]),c_0_23]),c_0_13])])).

cnf(c_0_66,negated_conjecture,
    ( v1_lattice3(esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk5_0,esk2_1(esk5_0),esk3_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_13])]),c_0_39]),c_0_38])).

cnf(c_0_67,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk8_4(X2,X1,X3,esk1_3(X1,X2,X3)))
    | ~ epred1_3(X3,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_58])).

cnf(c_0_68,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk8_4(X2,X1,X3,esk1_3(X1,X4,X3)))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X4,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_50])).

cnf(c_0_69,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(X1,esk6_0))
    | m1_subset_1(esk8_4(X1,esk5_0,esk6_0,esk1_3(esk5_0,X1,esk6_0)),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_59]),c_0_13])]),c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_26]),c_0_13])]),c_0_19]),c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_yellow_0(esk5_0,k2_tarski(esk6_0,esk7_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_73,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(X1,esk6_0))
    | r1_orders_2(esk5_0,X1,esk8_4(X1,esk5_0,esk6_0,esk1_3(esk5_0,X1,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_59]),c_0_13])]),c_0_65])).

cnf(c_0_74,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk8_4(X2,X1,X3,esk1_3(X1,X2,X3)))
    | ~ epred1_3(X3,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_58])).

cnf(c_0_75,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X4,esk8_4(X2,X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_76,plain,
    ( r1_orders_2(X2,esk1_3(X2,X3,X4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_77,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(X1,esk6_0))
    | m1_subset_1(esk8_4(X1,esk5_0,esk6_0,esk1_3(esk5_0,X1,esk6_0)),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_70])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_yellow_0(esk5_0,k2_tarski(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_70])])).

cnf(c_0_80,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(X1,esk6_0))
    | r1_orders_2(esk5_0,X1,esk8_4(X1,esk5_0,esk6_0,esk1_3(esk5_0,X1,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_70])])).

cnf(c_0_81,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(X1,esk6_0))
    | r1_orders_2(esk5_0,esk6_0,esk8_4(X1,esk5_0,esk6_0,esk1_3(esk5_0,X1,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_59]),c_0_13])]),c_0_65])).

cnf(c_0_82,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X4,esk8_4(X2,X1,X3,esk1_3(X1,X5,X4)))
    | ~ r1_orders_2(X1,X5,esk8_4(X2,X1,X3,esk1_3(X1,X5,X4)))
    | ~ r1_orders_2(X1,X3,esk1_3(X1,X5,X4))
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X5,X4))
    | ~ m1_subset_1(esk8_4(X2,X1,X3,esk1_3(X1,X5,X4)),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk8_4(esk7_0,esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_28]),c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk8_4(esk7_0,esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_78]),c_0_28]),c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_70])])).

cnf(c_0_86,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(X1,esk6_0))
    | r1_orders_2(esk5_0,esk6_0,esk8_4(X1,esk5_0,esk6_0,esk1_3(esk5_0,X1,esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_70])])).

cnf(c_0_87,plain,
    ( ~ epred1_3(esk6_0,esk5_0,esk7_0)
    | ~ r1_orders_2(esk5_0,esk6_0,esk8_4(esk7_0,esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0)))
    | ~ r1_orders_2(esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0))
    | ~ r1_orders_2(esk5_0,esk7_0,esk1_3(esk5_0,esk7_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_28]),c_0_84]),c_0_85]),c_0_78]),c_0_70]),c_0_13])]),c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( r1_orders_2(esk5_0,esk6_0,esk8_4(esk7_0,esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_78]),c_0_28]),c_0_79])).

cnf(c_0_89,plain,
    ( ~ epred1_3(esk6_0,esk5_0,esk7_0)
    | ~ r1_orders_2(esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0))
    | ~ r1_orders_2(esk5_0,esk7_0,esk1_3(esk5_0,esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_90,plain,
    ( ~ epred1_3(esk6_0,esk5_0,esk7_0)
    | ~ r1_orders_2(esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_58]),c_0_85]),c_0_78]),c_0_70]),c_0_13])])).

cnf(c_0_91,plain,
    ( ~ epred1_3(esk6_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_50]),c_0_78]),c_0_85]),c_0_70]),c_0_13])])).

cnf(c_0_92,negated_conjecture,
    ( epred1_3(esk6_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_70])])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_78])]),
    [proof]).

%------------------------------------------------------------------------------
