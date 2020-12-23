%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:10 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  104 (1320 expanded)
%              Number of clauses        :   93 ( 458 expanded)
%              Number of leaves         :    4 ( 309 expanded)
%              Depth                    :    9
%              Number of atoms          :  860 (20042 expanded)
%              Number of equality atoms :   96 (2452 expanded)
%              Maximal formula depth    :   22 (   9 average)
%              Maximal clause size      :   66 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t19_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k5_waybel_0(X1,X2) = k5_waybel_0(X1,X3)
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_0)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(c_0_3,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
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

fof(c_0_4,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
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
    inference(split_equiv,[status(thm)],[c_0_3])).

fof(c_0_5,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( r1_orders_2(X14,X15,X17)
        | X17 != k10_lattice3(X14,X15,X16)
        | ~ r1_yellow_0(X14,k2_tarski(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( r1_orders_2(X14,X16,X17)
        | X17 != k10_lattice3(X14,X15,X16)
        | ~ r1_yellow_0(X14,k2_tarski(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X14))
        | ~ r1_orders_2(X14,X15,X18)
        | ~ r1_orders_2(X14,X16,X18)
        | r1_orders_2(X14,X17,X18)
        | X17 != k10_lattice3(X14,X15,X16)
        | ~ r1_yellow_0(X14,k2_tarski(X15,X16))
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( X17 = k10_lattice3(X14,X15,X16)
        | m1_subset_1(esk4_4(X14,X15,X16,X17),u1_struct_0(X14))
        | ~ r1_orders_2(X14,X15,X17)
        | ~ r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( r1_yellow_0(X14,k2_tarski(X15,X16))
        | m1_subset_1(esk4_4(X14,X15,X16,X17),u1_struct_0(X14))
        | ~ r1_orders_2(X14,X15,X17)
        | ~ r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( X17 = k10_lattice3(X14,X15,X16)
        | r1_orders_2(X14,X15,esk4_4(X14,X15,X16,X17))
        | ~ r1_orders_2(X14,X15,X17)
        | ~ r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( r1_yellow_0(X14,k2_tarski(X15,X16))
        | r1_orders_2(X14,X15,esk4_4(X14,X15,X16,X17))
        | ~ r1_orders_2(X14,X15,X17)
        | ~ r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( X17 = k10_lattice3(X14,X15,X16)
        | r1_orders_2(X14,X16,esk4_4(X14,X15,X16,X17))
        | ~ r1_orders_2(X14,X15,X17)
        | ~ r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( r1_yellow_0(X14,k2_tarski(X15,X16))
        | r1_orders_2(X14,X16,esk4_4(X14,X15,X16,X17))
        | ~ r1_orders_2(X14,X15,X17)
        | ~ r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( X17 = k10_lattice3(X14,X15,X16)
        | ~ r1_orders_2(X14,X17,esk4_4(X14,X15,X16,X17))
        | ~ r1_orders_2(X14,X15,X17)
        | ~ r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) )
      & ( r1_yellow_0(X14,k2_tarski(X15,X16))
        | ~ r1_orders_2(X14,X17,esk4_4(X14,X15,X16,X17))
        | ~ r1_orders_2(X14,X15,X17)
        | ~ r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ epred1_3(X16,X15,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).

fof(c_0_6,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => epred1_3(X3,X2,X1) ) ) ) ),
    inference(apply_def,[status(thm)],[t18_yellow_0,c_0_3])).

cnf(c_0_7,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,X1,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_8,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X4,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X3,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

fof(c_0_10,plain,(
    ! [X8,X9,X10] :
      ( ~ v5_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | epred1_3(X10,X9,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k5_waybel_0(X1,X2) = k5_waybel_0(X1,X3)
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_waybel_0])).

cnf(c_0_12,plain,
    ( k10_lattice3(X1,X2,X3) = X3
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8]),
    [final]).

cnf(c_0_13,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | m1_subset_1(esk4_4(X2,X3,X4,X1),u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_14,plain,
    ( k10_lattice3(X1,X2,X3) = X2
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_9]),
    [final]).

cnf(c_0_15,plain,
    ( epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_16,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

fof(c_0_17,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v3_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r1_orders_2(X6,X7,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & k5_waybel_0(esk1_0,esk2_0) = k5_waybel_0(esk1_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_19,plain,
    ( k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5)) = esk4_4(X1,X3,X4,X5)
    | X5 = k10_lattice3(X1,X3,X4)
    | ~ epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)
    | ~ epred1_3(X4,X3,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X4,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_20,plain,
    ( k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5) = esk4_4(X1,X2,X3,X4)
    | X4 = k10_lattice3(X1,X2,X3)
    | ~ epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13]),
    [final]).

cnf(c_0_21,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | epred1_3(esk4_4(X2,X3,X4,X1),X5,X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13]),
    [final]).

cnf(c_0_22,plain,
    ( k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5) = esk4_4(X1,X2,X3,X4)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_16]),
    [final]).

cnf(c_0_23,plain,
    ( k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5)) = esk4_4(X1,X3,X4,X5)
    | r1_yellow_0(X1,k2_tarski(X3,X4))
    | ~ epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)
    | ~ epred1_3(X4,X3,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X4,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16]),
    [final]).

cnf(c_0_24,plain,
    ( epred1_3(esk4_4(X1,X2,X3,X4),X5,X1)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_31,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | X4 = k10_lattice3(X1,X2,X3)
    | X7 = k10_lattice3(X1,X5,X6)
    | ~ epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_32,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | X5 = k10_lattice3(X2,X6,X7)
    | epred1_3(esk4_4(X2,X6,X7,X5),esk4_4(X2,X3,X4,X1),X2)
    | ~ epred1_3(X7,X6,X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X7,X5)
    | ~ r1_orders_2(X2,X6,X5)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13]),
    [final]).

cnf(c_0_33,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | X7 = k10_lattice3(X1,X5,X6)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22]),
    [final]).

cnf(c_0_34,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | epred1_3(esk4_4(X2,X3,X4,X1),esk4_4(X2,X5,X6,X7),X2)
    | r1_yellow_0(X2,k2_tarski(X5,X6))
    | ~ epred1_3(X4,X3,X2)
    | ~ epred1_3(X6,X5,X2)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X6,X7)
    | ~ r1_orders_2(X2,X5,X7)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X7,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16]),
    [final]).

cnf(c_0_35,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_yellow_0(X1,k2_tarski(X5,X6))
    | ~ epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22]),
    [final]).

cnf(c_0_36,plain,
    ( epred1_3(esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7),X1)
    | r1_yellow_0(X1,k2_tarski(X5,X6))
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X3,X2,X1)
    | ~ epred1_3(X6,X5,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_16]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_29]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_30]),c_0_27]),c_0_28])]),c_0_29]),
    [final]).

cnf(c_0_40,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | X7 = k10_lattice3(X1,X5,X6)
    | X4 = k10_lattice3(X1,X2,X3)
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32]),
    [final]).

cnf(c_0_41,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | v2_struct_0(X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13]),
    [final]).

cnf(c_0_42,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | X7 = k10_lattice3(X1,X5,X6)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34]),
    [final]).

cnf(c_0_43,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | v2_struct_0(X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_16]),
    [final]).

cnf(c_0_44,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | r1_yellow_0(X1,k2_tarski(X5,X6))
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( k10_lattice3(esk1_0,esk2_0,X1) = esk2_0
    | ~ epred1_3(X1,esk2_0,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_26]),c_0_37])]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | epred1_3(esk4_4(esk1_0,X2,X3,X1),esk2_0,esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_26]),c_0_38]),c_0_27])]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( k10_lattice3(esk1_0,esk3_0,X1) = esk3_0
    | ~ epred1_3(X1,esk3_0,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_30]),c_0_39])]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | epred1_3(esk4_4(esk1_0,X2,X3,X1),esk3_0,esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_30]),c_0_38]),c_0_27])]),
    [final]).

cnf(c_0_49,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X4,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_50,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( epred1_3(esk4_4(esk1_0,X1,X2,X3),esk2_0,esk1_0)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_26]),c_0_38]),c_0_27])]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( epred1_3(esk4_4(esk1_0,X1,X2,X3),esk3_0,esk1_0)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_30]),c_0_38]),c_0_27])]),
    [final]).

cnf(c_0_53,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( epred1_3(esk2_0,X1,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_26]),c_0_38]),c_0_27])]),
    [final]).

cnf(c_0_55,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | X4 = k10_lattice3(X1,X2,X3)
    | X7 = k10_lattice3(X1,X5,X6)
    | v2_struct_0(X1)
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_41]),
    [final]).

cnf(c_0_56,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | X7 = k10_lattice3(X1,X5,X6)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | v2_struct_0(X1)
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_43]),
    [final]).

cnf(c_0_57,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_yellow_0(X1,k2_tarski(X5,X6))
    | v2_struct_0(X1)
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_43]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( esk4_4(esk1_0,X1,X2,X3) = esk2_0
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_19]),c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( esk4_4(esk1_0,X1,X2,X3) = esk3_0
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_19]),c_0_48])).

cnf(c_0_60,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( esk4_4(esk1_0,X1,X2,X3) = esk2_0
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23]),c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( esk4_4(esk1_0,X1,X2,X3) = esk3_0
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_23]),c_0_52])).

cnf(c_0_63,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_53]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( epred1_3(esk3_0,X1,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_30]),c_0_38]),c_0_27])]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( k10_lattice3(esk1_0,X1,esk2_0) = esk2_0
    | ~ epred1_3(esk2_0,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_26]),c_0_37])]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( epred1_3(esk2_0,esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_30]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_68,plain,
    ( r1_orders_2(X2,X5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k10_lattice3(X2,X3,X4)
    | ~ r1_yellow_0(X2,k2_tarski(X3,X4))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_69,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X4,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_70,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X4,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_71,plain,
    ( esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6) = esk4_4(X1,X2,X3,X4)
    | X6 = k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5)
    | X4 = k10_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),X6)
    | ~ r1_orders_2(X1,X5,X6)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_9]),
    [final]).

cnf(c_0_72,plain,
    ( esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6) = esk4_4(X1,X3,X4,X5)
    | X6 = k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5))
    | X5 = k10_lattice3(X1,X3,X4)
    | v2_struct_0(X1)
    | ~ epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)
    | ~ epred1_3(X4,X3,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6),esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,esk4_4(X1,X3,X4,X5),X6)
    | ~ r1_orders_2(X1,X2,X6)
    | ~ r1_orders_2(X1,X4,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_8]),
    [final]).

cnf(c_0_73,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | X4 = k10_lattice3(X1,X2,X3)
    | r1_yellow_0(X1,k2_tarski(X5,X6))
    | ~ epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X6,X5,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X6,X7)
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20]),
    [final]).

cnf(c_0_74,plain,
    ( esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6) = esk4_4(X1,X2,X3,X4)
    | X6 = k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | v2_struct_0(X1)
    | ~ epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),X6)
    | ~ r1_orders_2(X1,X5,X6)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_9]),
    [final]).

cnf(c_0_75,plain,
    ( esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6) = esk4_4(X1,X3,X4,X5)
    | X6 = k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5))
    | r1_yellow_0(X1,k2_tarski(X3,X4))
    | v2_struct_0(X1)
    | ~ epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)
    | ~ epred1_3(X4,X3,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6),esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,esk4_4(X1,X3,X4,X5),X6)
    | ~ r1_orders_2(X1,X2,X6)
    | ~ r1_orders_2(X1,X4,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_8]),
    [final]).

cnf(c_0_76,plain,
    ( esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6) = esk4_4(X1,X2,X3,X4)
    | r1_yellow_0(X1,k2_tarski(esk4_4(X1,X2,X3,X4),X5))
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | v2_struct_0(X1)
    | ~ epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),X6)
    | ~ r1_orders_2(X1,X5,X6)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_50]),
    [final]).

cnf(c_0_77,plain,
    ( esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6) = esk4_4(X1,X3,X4,X5)
    | r1_yellow_0(X1,k2_tarski(X2,esk4_4(X1,X3,X4,X5)))
    | r1_yellow_0(X1,k2_tarski(X3,X4))
    | v2_struct_0(X1)
    | ~ epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)
    | ~ epred1_3(X4,X3,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6),esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,esk4_4(X1,X3,X4,X5),X6)
    | ~ r1_orders_2(X1,X2,X6)
    | ~ r1_orders_2(X1,X4,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_53]),
    [final]).

cnf(c_0_78,plain,
    ( esk4_4(esk1_0,X1,X2,X3) = esk2_0
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_27]),c_0_28])]),c_0_29]),
    [final]).

cnf(c_0_79,plain,
    ( esk4_4(esk1_0,X1,X2,X3) = esk3_0
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_41]),c_0_27]),c_0_28])]),c_0_29]),
    [final]).

cnf(c_0_80,plain,
    ( r1_yellow_0(X1,k2_tarski(esk4_4(X1,X2,X3,X4),X5))
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_16]),
    [final]).

cnf(c_0_81,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_yellow_0(X2,k2_tarski(esk4_4(X2,X3,X4,X1),X5))
    | ~ epred1_3(X5,esk4_4(X2,X3,X4,X1),X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_13]),
    [final]).

cnf(c_0_82,plain,
    ( esk4_4(esk1_0,X1,X2,X3) = esk2_0
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_43]),c_0_27]),c_0_28])]),c_0_29]),
    [final]).

cnf(c_0_83,plain,
    ( esk4_4(esk1_0,X1,X2,X3) = esk3_0
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_43]),c_0_27]),c_0_28])]),c_0_29]),
    [final]).

cnf(c_0_84,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,esk4_4(X1,X3,X4,X5)))
    | r1_yellow_0(X1,k2_tarski(X3,X4))
    | ~ epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)
    | ~ epred1_3(X4,X3,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X4,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_16]),
    [final]).

cnf(c_0_85,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | epred1_3(esk4_4(X2,X5,X6,X7),esk4_4(X2,X3,X4,X1),X2)
    | r1_yellow_0(X2,k2_tarski(X5,X6))
    | ~ epred1_3(X6,X5,X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X6,X7)
    | ~ r1_orders_2(X2,X5,X7)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X7,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13]),
    [final]).

cnf(c_0_86,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_yellow_0(X2,k2_tarski(X5,esk4_4(X2,X3,X4,X1)))
    | ~ epred1_3(esk4_4(X2,X3,X4,X1),X5,X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_13]),
    [final]).

cnf(c_0_87,plain,
    ( epred1_3(esk2_0,esk4_4(esk1_0,X1,X2,X3),esk1_0)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_16]),
    [final]).

cnf(c_0_88,plain,
    ( epred1_3(esk3_0,esk4_4(esk1_0,X1,X2,X3),esk1_0)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_16]),
    [final]).

cnf(c_0_89,plain,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | epred1_3(esk2_0,esk4_4(esk1_0,X2,X3,X1),esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_13]),
    [final]).

cnf(c_0_90,plain,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | epred1_3(esk3_0,esk4_4(esk1_0,X2,X3,X1),esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_13]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(esk2_0,X1))
    | ~ epred1_3(X1,esk2_0,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_26]),c_0_37])]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(esk3_0,X1))
    | ~ epred1_3(X1,esk3_0,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_30]),c_0_39])]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,esk2_0))
    | ~ epred1_3(esk2_0,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_26]),c_0_37])]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,esk3_0))
    | ~ epred1_3(esk3_0,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_30]),c_0_39])]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_47]),c_0_66])]),c_0_67]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( k10_lattice3(esk1_0,X1,esk3_0) = esk3_0
    | ~ epred1_3(esk3_0,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_30]),c_0_39])]),
    [final]).

cnf(c_0_97,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_68]),
    [final]).

cnf(c_0_98,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_69]),
    [final]).

cnf(c_0_99,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ epred1_3(X2,X3,X1)
    | ~ r1_yellow_0(X1,k2_tarski(X3,X2))
    | ~ m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_70]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( epred1_3(esk2_0,esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_26]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( epred1_3(esk3_0,esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_26]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( epred1_3(esk3_0,esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_30]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( k5_waybel_0(esk1_0,esk2_0) = k5_waybel_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n016.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 17:30:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.13/0.35  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.013 s
% 0.13/0.35  # Presaturation interreduction done
% 0.13/0.35  
% 0.13/0.35  # No proof found!
% 0.13/0.35  # SZS status CounterSatisfiable
% 0.13/0.35  # SZS output start Saturation
% 0.13/0.35  fof(t18_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3)))=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))&(((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))=>(X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_0)).
% 0.13/0.35  fof(t19_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k5_waybel_0(X1,X2)=k5_waybel_0(X1,X3)=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_waybel_0)).
% 0.13/0.35  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.13/0.35  fof(c_0_3, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3)))=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))&(((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))=>(X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3))))))), introduced(definition)).
% 0.13/0.35  fof(c_0_4, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3)))=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))&(((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))=>(X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3))))))), inference(split_equiv,[status(thm)],[c_0_3])).
% 0.13/0.35  fof(c_0_5, plain, ![X14, X15, X16, X17, X18]:((((r1_orders_2(X14,X15,X17)|(X17!=k10_lattice3(X14,X15,X16)|~r1_yellow_0(X14,k2_tarski(X15,X16)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14))&(r1_orders_2(X14,X16,X17)|(X17!=k10_lattice3(X14,X15,X16)|~r1_yellow_0(X14,k2_tarski(X15,X16)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14)))&(~m1_subset_1(X18,u1_struct_0(X14))|(~r1_orders_2(X14,X15,X18)|~r1_orders_2(X14,X16,X18)|r1_orders_2(X14,X17,X18))|(X17!=k10_lattice3(X14,X15,X16)|~r1_yellow_0(X14,k2_tarski(X15,X16)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14)))&(((X17=k10_lattice3(X14,X15,X16)|(m1_subset_1(esk4_4(X14,X15,X16,X17),u1_struct_0(X14))|(~r1_orders_2(X14,X15,X17)|~r1_orders_2(X14,X16,X17)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14))&(r1_yellow_0(X14,k2_tarski(X15,X16))|(m1_subset_1(esk4_4(X14,X15,X16,X17),u1_struct_0(X14))|(~r1_orders_2(X14,X15,X17)|~r1_orders_2(X14,X16,X17)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14)))&((((X17=k10_lattice3(X14,X15,X16)|(r1_orders_2(X14,X15,esk4_4(X14,X15,X16,X17))|(~r1_orders_2(X14,X15,X17)|~r1_orders_2(X14,X16,X17)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14))&(r1_yellow_0(X14,k2_tarski(X15,X16))|(r1_orders_2(X14,X15,esk4_4(X14,X15,X16,X17))|(~r1_orders_2(X14,X15,X17)|~r1_orders_2(X14,X16,X17)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14)))&((X17=k10_lattice3(X14,X15,X16)|(r1_orders_2(X14,X16,esk4_4(X14,X15,X16,X17))|(~r1_orders_2(X14,X15,X17)|~r1_orders_2(X14,X16,X17)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14))&(r1_yellow_0(X14,k2_tarski(X15,X16))|(r1_orders_2(X14,X16,esk4_4(X14,X15,X16,X17))|(~r1_orders_2(X14,X15,X17)|~r1_orders_2(X14,X16,X17)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14))))&((X17=k10_lattice3(X14,X15,X16)|(~r1_orders_2(X14,X17,esk4_4(X14,X15,X16,X17))|(~r1_orders_2(X14,X15,X17)|~r1_orders_2(X14,X16,X17)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14))&(r1_yellow_0(X14,k2_tarski(X15,X16))|(~r1_orders_2(X14,X17,esk4_4(X14,X15,X16,X17))|(~r1_orders_2(X14,X15,X17)|~r1_orders_2(X14,X16,X17)))|~m1_subset_1(X17,u1_struct_0(X14))|~epred1_3(X16,X15,X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).
% 0.13/0.35  fof(c_0_6, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>epred1_3(X3,X2,X1)))), inference(apply_def,[status(thm)],[t18_yellow_0, c_0_3])).
% 0.13/0.35  cnf(c_0_7, plain, (X1=k10_lattice3(X2,X3,X4)|~r1_orders_2(X2,X1,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.35  cnf(c_0_8, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X4,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.35  cnf(c_0_9, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X3,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.35  fof(c_0_10, plain, ![X8, X9, X10]:(~v5_orders_2(X8)|~l1_orders_2(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|(~m1_subset_1(X10,u1_struct_0(X8))|epred1_3(X10,X9,X8)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.35  fof(c_0_11, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k5_waybel_0(X1,X2)=k5_waybel_0(X1,X3)=>X2=X3))))), inference(assume_negation,[status(cth)],[t19_waybel_0])).
% 0.13/0.35  cnf(c_0_12, plain, (k10_lattice3(X1,X2,X3)=X3|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_7, c_0_8]), ['final']).
% 0.13/0.35  cnf(c_0_13, plain, (X1=k10_lattice3(X2,X3,X4)|m1_subset_1(esk4_4(X2,X3,X4,X1),u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.35  cnf(c_0_14, plain, (k10_lattice3(X1,X2,X3)=X2|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X2)|~r1_orders_2(X1,X2,X2)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_7, c_0_9]), ['final']).
% 0.13/0.35  cnf(c_0_15, plain, (epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.35  cnf(c_0_16, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.35  fof(c_0_17, plain, ![X6, X7]:(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|(~m1_subset_1(X7,u1_struct_0(X6))|r1_orders_2(X6,X7,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.13/0.35  fof(c_0_18, negated_conjecture, ((((~v2_struct_0(esk1_0)&v3_orders_2(esk1_0))&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(k5_waybel_0(esk1_0,esk2_0)=k5_waybel_0(esk1_0,esk3_0)&esk2_0!=esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.13/0.35  cnf(c_0_19, plain, (k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5))=esk4_4(X1,X3,X4,X5)|X5=k10_lattice3(X1,X3,X4)|~epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)|~epred1_3(X4,X3,X1)|~r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X4,X5)|~r1_orders_2(X1,X3,X5)|~m1_subset_1(X5,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_20, plain, (k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5)=esk4_4(X1,X2,X3,X4)|X4=k10_lattice3(X1,X2,X3)|~epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_14, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_21, plain, (X1=k10_lattice3(X2,X3,X4)|epred1_3(esk4_4(X2,X3,X4,X1),X5,X2)|~epred1_3(X4,X3,X2)|~v5_orders_2(X2)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_15, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_22, plain, (k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5)=esk4_4(X1,X2,X3,X4)|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_14, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_23, plain, (k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5))=esk4_4(X1,X3,X4,X5)|r1_yellow_0(X1,k2_tarski(X3,X4))|~epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)|~epred1_3(X4,X3,X1)|~r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X4,X5)|~r1_orders_2(X1,X3,X5)|~m1_subset_1(X5,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_12, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_24, plain, (epred1_3(esk4_4(X1,X2,X3,X4),X5,X1)|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_25, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.35  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.35  cnf(c_0_27, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.35  cnf(c_0_28, negated_conjecture, (v3_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.35  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.35  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.35  cnf(c_0_31, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X4=k10_lattice3(X1,X2,X3)|X7=k10_lattice3(X1,X5,X6)|~epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.13/0.35  cnf(c_0_32, plain, (X1=k10_lattice3(X2,X3,X4)|X5=k10_lattice3(X2,X6,X7)|epred1_3(esk4_4(X2,X6,X7,X5),esk4_4(X2,X3,X4,X1),X2)|~epred1_3(X7,X6,X2)|~epred1_3(X4,X3,X2)|~v5_orders_2(X2)|~r1_orders_2(X2,X7,X5)|~r1_orders_2(X2,X6,X5)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_21, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_33, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X7=k10_lattice3(X1,X5,X6)|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_19, c_0_22]), ['final']).
% 0.13/0.35  cnf(c_0_34, plain, (X1=k10_lattice3(X2,X3,X4)|epred1_3(esk4_4(X2,X3,X4,X1),esk4_4(X2,X5,X6,X7),X2)|r1_yellow_0(X2,k2_tarski(X5,X6))|~epred1_3(X4,X3,X2)|~epred1_3(X6,X5,X2)|~v5_orders_2(X2)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X6,X7)|~r1_orders_2(X2,X5,X7)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X7,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_21, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_35, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|r1_yellow_0(X1,k2_tarski(X2,X3))|r1_yellow_0(X1,k2_tarski(X5,X6))|~epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_23, c_0_22]), ['final']).
% 0.13/0.35  cnf(c_0_36, plain, (epred1_3(esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7),X1)|r1_yellow_0(X1,k2_tarski(X5,X6))|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X3,X2,X1)|~epred1_3(X6,X5,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_24, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_37, negated_conjecture, (r1_orders_2(esk1_0,esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])]), c_0_29]), ['final']).
% 0.13/0.35  cnf(c_0_38, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.35  cnf(c_0_39, negated_conjecture, (r1_orders_2(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_30]), c_0_27]), c_0_28])]), c_0_29]), ['final']).
% 0.13/0.35  cnf(c_0_40, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X7=k10_lattice3(X1,X5,X6)|X4=k10_lattice3(X1,X2,X3)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32]), ['final']).
% 0.13/0.35  cnf(c_0_41, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))|v2_struct_0(X2)|~epred1_3(X4,X3,X2)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_25, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_42, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X7=k10_lattice3(X1,X5,X6)|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34]), ['final']).
% 0.13/0.35  cnf(c_0_43, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|v2_struct_0(X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_25, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_44, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|r1_yellow_0(X1,k2_tarski(X5,X6))|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.13/0.35  cnf(c_0_45, negated_conjecture, (k10_lattice3(esk1_0,esk2_0,X1)=esk2_0|~epred1_3(X1,esk2_0,esk1_0)|~r1_orders_2(esk1_0,X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_26]), c_0_37])]), ['final']).
% 0.13/0.35  cnf(c_0_46, negated_conjecture, (X1=k10_lattice3(esk1_0,X2,X3)|epred1_3(esk4_4(esk1_0,X2,X3,X1),esk2_0,esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_26]), c_0_38]), c_0_27])]), ['final']).
% 0.13/0.35  cnf(c_0_47, negated_conjecture, (k10_lattice3(esk1_0,esk3_0,X1)=esk3_0|~epred1_3(X1,esk3_0,esk1_0)|~r1_orders_2(esk1_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_30]), c_0_39])]), ['final']).
% 0.13/0.35  cnf(c_0_48, negated_conjecture, (X1=k10_lattice3(esk1_0,X2,X3)|epred1_3(esk4_4(esk1_0,X2,X3,X1),esk3_0,esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_30]), c_0_38]), c_0_27])]), ['final']).
% 0.13/0.35  cnf(c_0_49, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|~r1_orders_2(X1,X4,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.35  cnf(c_0_50, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,X2,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.35  cnf(c_0_51, negated_conjecture, (epred1_3(esk4_4(esk1_0,X1,X2,X3),esk2_0,esk1_0)|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_26]), c_0_38]), c_0_27])]), ['final']).
% 0.13/0.35  cnf(c_0_52, negated_conjecture, (epred1_3(esk4_4(esk1_0,X1,X2,X3),esk3_0,esk1_0)|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_30]), c_0_38]), c_0_27])]), ['final']).
% 0.13/0.35  cnf(c_0_53, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,X3,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.35  cnf(c_0_54, negated_conjecture, (epred1_3(esk2_0,X1,esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_26]), c_0_38]), c_0_27])]), ['final']).
% 0.13/0.35  cnf(c_0_55, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X4=k10_lattice3(X1,X2,X3)|X7=k10_lattice3(X1,X5,X6)|v2_struct_0(X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_41]), ['final']).
% 0.13/0.35  cnf(c_0_56, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X7=k10_lattice3(X1,X5,X6)|r1_yellow_0(X1,k2_tarski(X2,X3))|v2_struct_0(X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_43]), ['final']).
% 0.13/0.35  cnf(c_0_57, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|r1_yellow_0(X1,k2_tarski(X2,X3))|r1_yellow_0(X1,k2_tarski(X5,X6))|v2_struct_0(X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_43]), ['final']).
% 0.13/0.35  cnf(c_0_58, negated_conjecture, (esk4_4(esk1_0,X1,X2,X3)=esk2_0|X3=k10_lattice3(esk1_0,X1,X2)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)|~r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_19]), c_0_46])).
% 0.13/0.35  cnf(c_0_59, negated_conjecture, (esk4_4(esk1_0,X1,X2,X3)=esk3_0|X3=k10_lattice3(esk1_0,X1,X2)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)|~r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_19]), c_0_48])).
% 0.13/0.35  cnf(c_0_60, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X2)|~r1_orders_2(X1,X2,X2)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50]), ['final']).
% 0.13/0.35  cnf(c_0_61, negated_conjecture, (esk4_4(esk1_0,X1,X2,X3)=esk2_0|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)|~r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_23]), c_0_51])).
% 0.13/0.35  cnf(c_0_62, negated_conjecture, (esk4_4(esk1_0,X1,X2,X3)=esk3_0|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)|~r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_23]), c_0_52])).
% 0.13/0.35  cnf(c_0_63, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_49, c_0_53]), ['final']).
% 0.13/0.35  cnf(c_0_64, negated_conjecture, (epred1_3(esk3_0,X1,esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_30]), c_0_38]), c_0_27])]), ['final']).
% 0.13/0.35  cnf(c_0_65, negated_conjecture, (k10_lattice3(esk1_0,X1,esk2_0)=esk2_0|~epred1_3(esk2_0,X1,esk1_0)|~r1_orders_2(esk1_0,X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_26]), c_0_37])]), ['final']).
% 0.13/0.35  cnf(c_0_66, negated_conjecture, (epred1_3(esk2_0,esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_54, c_0_30]), ['final']).
% 0.13/0.35  cnf(c_0_67, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.35  cnf(c_0_68, plain, (r1_orders_2(X2,X5,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|X5!=k10_lattice3(X2,X3,X4)|~r1_yellow_0(X2,k2_tarski(X3,X4))|~m1_subset_1(X5,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_69, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X2,X4)|~r1_yellow_0(X1,k2_tarski(X2,X4))|~m1_subset_1(X3,u1_struct_0(X1))|~epred1_3(X4,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_70, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X4,X2)|~r1_yellow_0(X1,k2_tarski(X4,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~epred1_3(X2,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_71, plain, (esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6)=esk4_4(X1,X2,X3,X4)|X6=k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5)|X4=k10_lattice3(X1,X2,X3)|v2_struct_0(X1)|~epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),X6)|~r1_orders_2(X1,X5,X6)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_55, c_0_9]), ['final']).
% 0.13/0.35  cnf(c_0_72, plain, (esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6)=esk4_4(X1,X3,X4,X5)|X6=k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5))|X5=k10_lattice3(X1,X3,X4)|v2_struct_0(X1)|~epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)|~epred1_3(X4,X3,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6),esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,esk4_4(X1,X3,X4,X5),X6)|~r1_orders_2(X1,X2,X6)|~r1_orders_2(X1,X4,X5)|~r1_orders_2(X1,X3,X5)|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_55, c_0_8]), ['final']).
% 0.13/0.35  cnf(c_0_73, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X4=k10_lattice3(X1,X2,X3)|r1_yellow_0(X1,k2_tarski(X5,X6))|~epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_23, c_0_20]), ['final']).
% 0.13/0.35  cnf(c_0_74, plain, (esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6)=esk4_4(X1,X2,X3,X4)|X6=k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5)|r1_yellow_0(X1,k2_tarski(X2,X3))|v2_struct_0(X1)|~epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),X6)|~r1_orders_2(X1,X5,X6)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_56, c_0_9]), ['final']).
% 0.13/0.35  cnf(c_0_75, plain, (esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6)=esk4_4(X1,X3,X4,X5)|X6=k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5))|r1_yellow_0(X1,k2_tarski(X3,X4))|v2_struct_0(X1)|~epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)|~epred1_3(X4,X3,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6),esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,esk4_4(X1,X3,X4,X5),X6)|~r1_orders_2(X1,X2,X6)|~r1_orders_2(X1,X4,X5)|~r1_orders_2(X1,X3,X5)|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_56, c_0_8]), ['final']).
% 0.13/0.35  cnf(c_0_76, plain, (esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6)=esk4_4(X1,X2,X3,X4)|r1_yellow_0(X1,k2_tarski(esk4_4(X1,X2,X3,X4),X5))|r1_yellow_0(X1,k2_tarski(X2,X3))|v2_struct_0(X1)|~epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,esk4_4(X1,X2,X3,X4),X5,X6),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),X6)|~r1_orders_2(X1,X5,X6)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_57, c_0_50]), ['final']).
% 0.13/0.35  cnf(c_0_77, plain, (esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6)=esk4_4(X1,X3,X4,X5)|r1_yellow_0(X1,k2_tarski(X2,esk4_4(X1,X3,X4,X5)))|r1_yellow_0(X1,k2_tarski(X3,X4))|v2_struct_0(X1)|~epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)|~epred1_3(X4,X3,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X2,esk4_4(X1,X3,X4,X5),X6),esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,esk4_4(X1,X3,X4,X5),X6)|~r1_orders_2(X1,X2,X6)|~r1_orders_2(X1,X4,X5)|~r1_orders_2(X1,X3,X5)|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_57, c_0_53]), ['final']).
% 0.13/0.35  cnf(c_0_78, plain, (esk4_4(esk1_0,X1,X2,X3)=esk2_0|X3=k10_lattice3(esk1_0,X1,X2)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)|~r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_27]), c_0_28])]), c_0_29]), ['final']).
% 0.13/0.35  cnf(c_0_79, plain, (esk4_4(esk1_0,X1,X2,X3)=esk3_0|X3=k10_lattice3(esk1_0,X1,X2)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)|~r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_41]), c_0_27]), c_0_28])]), c_0_29]), ['final']).
% 0.13/0.35  cnf(c_0_80, plain, (r1_yellow_0(X1,k2_tarski(esk4_4(X1,X2,X3,X4),X5))|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_60, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_81, plain, (X1=k10_lattice3(X2,X3,X4)|r1_yellow_0(X2,k2_tarski(esk4_4(X2,X3,X4,X1),X5))|~epred1_3(X5,esk4_4(X2,X3,X4,X1),X2)|~epred1_3(X4,X3,X2)|~r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_60, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_82, plain, (esk4_4(esk1_0,X1,X2,X3)=esk2_0|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)|~r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_43]), c_0_27]), c_0_28])]), c_0_29]), ['final']).
% 0.13/0.35  cnf(c_0_83, plain, (esk4_4(esk1_0,X1,X2,X3)=esk3_0|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)|~r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_43]), c_0_27]), c_0_28])]), c_0_29]), ['final']).
% 0.13/0.35  cnf(c_0_84, plain, (r1_yellow_0(X1,k2_tarski(X2,esk4_4(X1,X3,X4,X5)))|r1_yellow_0(X1,k2_tarski(X3,X4))|~epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)|~epred1_3(X4,X3,X1)|~r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X4,X5)|~r1_orders_2(X1,X3,X5)|~m1_subset_1(X5,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_63, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_85, plain, (X1=k10_lattice3(X2,X3,X4)|epred1_3(esk4_4(X2,X5,X6,X7),esk4_4(X2,X3,X4,X1),X2)|r1_yellow_0(X2,k2_tarski(X5,X6))|~epred1_3(X6,X5,X2)|~epred1_3(X4,X3,X2)|~v5_orders_2(X2)|~r1_orders_2(X2,X6,X7)|~r1_orders_2(X2,X5,X7)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X7,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_24, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_86, plain, (X1=k10_lattice3(X2,X3,X4)|r1_yellow_0(X2,k2_tarski(X5,esk4_4(X2,X3,X4,X1)))|~epred1_3(esk4_4(X2,X3,X4,X1),X5,X2)|~epred1_3(X4,X3,X2)|~r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_63, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_87, plain, (epred1_3(esk2_0,esk4_4(esk1_0,X1,X2,X3),esk1_0)|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_54, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_88, plain, (epred1_3(esk3_0,esk4_4(esk1_0,X1,X2,X3),esk1_0)|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_64, c_0_16]), ['final']).
% 0.13/0.35  cnf(c_0_89, plain, (X1=k10_lattice3(esk1_0,X2,X3)|epred1_3(esk2_0,esk4_4(esk1_0,X2,X3,X1),esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_54, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_90, plain, (X1=k10_lattice3(esk1_0,X2,X3)|epred1_3(esk3_0,esk4_4(esk1_0,X2,X3,X1),esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_64, c_0_13]), ['final']).
% 0.13/0.35  cnf(c_0_91, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(esk2_0,X1))|~epred1_3(X1,esk2_0,esk1_0)|~r1_orders_2(esk1_0,X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_26]), c_0_37])]), ['final']).
% 0.13/0.35  cnf(c_0_92, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(esk3_0,X1))|~epred1_3(X1,esk3_0,esk1_0)|~r1_orders_2(esk1_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_30]), c_0_39])]), ['final']).
% 0.13/0.35  cnf(c_0_93, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(X1,esk2_0))|~epred1_3(esk2_0,X1,esk1_0)|~r1_orders_2(esk1_0,X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_26]), c_0_37])]), ['final']).
% 0.13/0.35  cnf(c_0_94, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(X1,esk3_0))|~epred1_3(esk3_0,X1,esk1_0)|~r1_orders_2(esk1_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_30]), c_0_39])]), ['final']).
% 0.13/0.35  cnf(c_0_95, negated_conjecture, (~r1_orders_2(esk1_0,esk3_0,esk2_0)|~r1_orders_2(esk1_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_47]), c_0_66])]), c_0_67]), ['final']).
% 0.13/0.35  cnf(c_0_96, negated_conjecture, (k10_lattice3(esk1_0,X1,esk3_0)=esk3_0|~epred1_3(esk3_0,X1,esk1_0)|~r1_orders_2(esk1_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_30]), c_0_39])]), ['final']).
% 0.13/0.35  cnf(c_0_97, plain, (r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)|~epred1_3(X3,X2,X1)|~r1_yellow_0(X1,k2_tarski(X2,X3))|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_68]), ['final']).
% 0.13/0.35  cnf(c_0_98, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))|~epred1_3(X3,X2,X1)|~r1_yellow_0(X1,k2_tarski(X2,X3))|~m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), inference(er,[status(thm)],[c_0_69]), ['final']).
% 0.13/0.35  cnf(c_0_99, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))|~epred1_3(X2,X3,X1)|~r1_yellow_0(X1,k2_tarski(X3,X2))|~m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1))), inference(er,[status(thm)],[c_0_70]), ['final']).
% 0.13/0.35  cnf(c_0_100, negated_conjecture, (epred1_3(esk2_0,esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_54, c_0_26]), ['final']).
% 0.13/0.35  cnf(c_0_101, negated_conjecture, (epred1_3(esk3_0,esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_64, c_0_26]), ['final']).
% 0.13/0.35  cnf(c_0_102, negated_conjecture, (epred1_3(esk3_0,esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_64, c_0_30]), ['final']).
% 0.13/0.35  cnf(c_0_103, negated_conjecture, (k5_waybel_0(esk1_0,esk2_0)=k5_waybel_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.35  # SZS output end Saturation
% 0.13/0.35  # Proof object total steps             : 104
% 0.13/0.35  # Proof object clause steps            : 93
% 0.13/0.35  # Proof object formula steps           : 11
% 0.13/0.35  # Proof object conjectures             : 36
% 0.13/0.35  # Proof object clause conjectures      : 33
% 0.13/0.35  # Proof object formula conjectures     : 3
% 0.13/0.35  # Proof object initial clauses used    : 21
% 0.13/0.35  # Proof object initial formulas used   : 3
% 0.13/0.35  # Proof object generating inferences   : 69
% 0.13/0.35  # Proof object simplifying inferences  : 71
% 0.13/0.35  # Parsed axioms                        : 3
% 0.13/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.35  # Initial clauses                      : 21
% 0.13/0.35  # Removed in clause preprocessing      : 0
% 0.13/0.35  # Initial clauses in saturation        : 21
% 0.13/0.35  # Processed clauses                    : 145
% 0.13/0.35  # ...of these trivial                  : 0
% 0.13/0.35  # ...subsumed                          : 31
% 0.13/0.35  # ...remaining for further processing  : 114
% 0.13/0.35  # Other redundant clauses eliminated   : 3
% 0.13/0.35  # Clauses deleted for lack of memory   : 0
% 0.13/0.35  # Backward-subsumed                    : 4
% 0.13/0.35  # Backward-rewritten                   : 0
% 0.13/0.35  # Generated clauses                    : 131
% 0.13/0.35  # ...of the previous two non-trivial   : 107
% 0.13/0.35  # Contextual simplify-reflections      : 7
% 0.13/0.35  # Paramodulations                      : 128
% 0.13/0.35  # Factorizations                       : 0
% 0.13/0.35  # Equation resolutions                 : 3
% 0.13/0.35  # Propositional unsat checks           : 0
% 0.13/0.35  #    Propositional check models        : 0
% 0.13/0.35  #    Propositional check unsatisfiable : 0
% 0.13/0.35  #    Propositional clauses             : 0
% 0.13/0.35  #    Propositional clauses after purity: 0
% 0.13/0.35  #    Propositional unsat core size     : 0
% 0.13/0.35  #    Propositional preprocessing time  : 0.000
% 0.13/0.35  #    Propositional encoding time       : 0.000
% 0.13/0.35  #    Propositional solver time         : 0.000
% 0.13/0.35  #    Success case prop preproc time    : 0.000
% 0.13/0.35  #    Success case prop encoding time   : 0.000
% 0.13/0.35  #    Success case prop solver time     : 0.000
% 0.13/0.35  # Current number of processed clauses  : 86
% 0.13/0.35  #    Positive orientable unit clauses  : 12
% 0.13/0.35  #    Positive unorientable unit clauses: 0
% 0.13/0.35  #    Negative unit clauses             : 2
% 0.13/0.35  #    Non-unit-clauses                  : 72
% 0.13/0.35  # Current number of unprocessed clauses: 0
% 0.13/0.35  # ...number of literals in the above   : 0
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 25
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 6619
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 612
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 42
% 0.13/0.35  # Unit Clause-clause subsumption calls : 6
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.35  # BW rewrite match attempts            : 0
% 0.13/0.35  # BW rewrite match successes           : 0
% 0.13/0.35  # Condensation attempts                : 0
% 0.13/0.35  # Condensation successes               : 0
% 0.13/0.35  # Termbank termtop insertions          : 9252
% 0.13/0.35  
% 0.13/0.35  # -------------------------------------------------
% 0.13/0.35  # User time                : 0.023 s
% 0.13/0.35  # System time              : 0.002 s
% 0.13/0.35  # Total time               : 0.025 s
% 0.13/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
