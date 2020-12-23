%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:11 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  131 (2620 expanded)
%              Number of clauses        :  118 ( 872 expanded)
%              Number of leaves         :    5 ( 618 expanded)
%              Depth                    :    9
%              Number of atoms          : 1012 (32419 expanded)
%              Number of equality atoms :  101 (4343 expanded)
%              Maximal formula depth    :   22 (   8 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_0)).

fof(t20_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k6_waybel_0(X1,X2) = k6_waybel_0(X1,X3)
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_0)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(c_0_4,plain,(
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

fof(c_0_5,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( r1_orders_2(X18,X19,X21)
        | X21 != k10_lattice3(X18,X19,X20)
        | ~ r1_yellow_0(X18,k2_tarski(X19,X20))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( r1_orders_2(X18,X20,X21)
        | X21 != k10_lattice3(X18,X19,X20)
        | ~ r1_yellow_0(X18,k2_tarski(X19,X20))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X18))
        | ~ r1_orders_2(X18,X19,X22)
        | ~ r1_orders_2(X18,X20,X22)
        | r1_orders_2(X18,X21,X22)
        | X21 != k10_lattice3(X18,X19,X20)
        | ~ r1_yellow_0(X18,k2_tarski(X19,X20))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( X21 = k10_lattice3(X18,X19,X20)
        | m1_subset_1(esk4_4(X18,X19,X20,X21),u1_struct_0(X18))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( r1_yellow_0(X18,k2_tarski(X19,X20))
        | m1_subset_1(esk4_4(X18,X19,X20,X21),u1_struct_0(X18))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( X21 = k10_lattice3(X18,X19,X20)
        | r1_orders_2(X18,X19,esk4_4(X18,X19,X20,X21))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( r1_yellow_0(X18,k2_tarski(X19,X20))
        | r1_orders_2(X18,X19,esk4_4(X18,X19,X20,X21))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( X21 = k10_lattice3(X18,X19,X20)
        | r1_orders_2(X18,X20,esk4_4(X18,X19,X20,X21))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( r1_yellow_0(X18,k2_tarski(X19,X20))
        | r1_orders_2(X18,X20,esk4_4(X18,X19,X20,X21))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( X21 = k10_lattice3(X18,X19,X20)
        | ~ r1_orders_2(X18,X21,esk4_4(X18,X19,X20,X21))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) )
      & ( r1_yellow_0(X18,k2_tarski(X19,X20))
        | ~ r1_orders_2(X18,X21,esk4_4(X18,X19,X20,X21))
        | ~ r1_orders_2(X18,X19,X21)
        | ~ r1_orders_2(X18,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ epred1_3(X20,X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_7,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => epred1_3(X3,X2,X1) ) ) ) ),
    inference(apply_def,[status(thm)],[t18_yellow_0,c_0_4])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k6_waybel_0(X1,X2) = k6_waybel_0(X1,X3)
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_waybel_0])).

cnf(c_0_9,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,X1,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X4,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X3,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ~ v5_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | epred1_3(X14,X13,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_13,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v3_orders_2(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | r3_orders_2(X9,X10,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & k6_waybel_0(esk1_0,esk2_0) = k6_waybel_0(esk1_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_15,plain,
    ( k10_lattice3(X1,X2,X3) = X3
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_16,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_17,plain,
    ( k10_lattice3(X1,X2,X3) = X2
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_11]),
    [final]).

cnf(c_0_18,plain,
    ( epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r3_orders_2(X6,X7,X8)
        | r1_orders_2(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) )
      & ( ~ r1_orders_2(X6,X7,X8)
        | r3_orders_2(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_25,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | m1_subset_1(esk4_4(X2,X3,X4,X1),u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_26,plain,
    ( k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5)) = esk4_4(X1,X3,X4,X5)
    | r1_yellow_0(X1,k2_tarski(X3,X4))
    | ~ epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)
    | ~ epred1_3(X4,X3,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X4,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_27,plain,
    ( k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5) = esk4_4(X1,X2,X3,X4)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16]),
    [final]).

cnf(c_0_28,plain,
    ( epred1_3(esk4_4(X1,X2,X3,X4),X5,X1)
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16]),
    [final]).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),
    [final]).

cnf(c_0_31,plain,
    ( k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5) = esk4_4(X1,X2,X3,X4)
    | X4 = k10_lattice3(X1,X2,X3)
    | ~ epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_25]),
    [final]).

cnf(c_0_32,plain,
    ( k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5)) = esk4_4(X1,X3,X4,X5)
    | X5 = k10_lattice3(X1,X3,X4)
    | ~ epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)
    | ~ epred1_3(X4,X3,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X4,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_25]),
    [final]).

cnf(c_0_33,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | epred1_3(esk4_4(X2,X3,X4,X1),X5,X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
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
    inference(spm,[status(thm)],[c_0_26,c_0_27]),
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
    inference(spm,[status(thm)],[c_0_28,c_0_16]),
    [final]).

cnf(c_0_37,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X4,esk4_4(X1,X2,X3,X5))
    | v2_struct_0(X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ r1_orders_2(X1,X2,X5)
    | ~ r3_orders_2(X1,X4,esk4_4(X1,X2,X3,X5))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_16]),
    [final]).

cnf(c_0_38,plain,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | r3_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16]),
    [final]).

cnf(c_0_39,plain,
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
    inference(spm,[status(thm)],[c_0_26,c_0_31]),
    [final]).

cnf(c_0_40,plain,
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
    inference(spm,[status(thm)],[c_0_28,c_0_25]),
    [final]).

cnf(c_0_41,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))
    | v2_struct_0(X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r3_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25]),
    [final]).

cnf(c_0_42,plain,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | r3_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk4_4(esk1_0,X2,X3,X1))
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25]),
    [final]).

cnf(c_0_43,plain,
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
    inference(spm,[status(thm)],[c_0_32,c_0_31]),
    [final]).

cnf(c_0_44,plain,
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
    inference(spm,[status(thm)],[c_0_33,c_0_25]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r3_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_34]),c_0_22]),c_0_23])]),c_0_24]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( r3_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_34]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r3_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r3_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_50,plain,
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

cnf(c_0_51,plain,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_22]),c_0_23])]),c_0_24]),c_0_16]),
    [final]).

cnf(c_0_52,plain,
    ( esk4_4(X1,X2,X3,X4) = esk4_4(X1,X5,X6,X7)
    | X4 = k10_lattice3(X1,X2,X3)
    | r1_yellow_0(X1,k2_tarski(X5,X6))
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
    inference(spm,[status(thm)],[c_0_39,c_0_40]),
    [final]).

cnf(c_0_53,plain,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk4_4(esk1_0,X2,X3,X1))
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_22]),c_0_23])]),c_0_24]),c_0_25]),
    [final]).

cnf(c_0_54,plain,
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
    inference(spm,[status(thm)],[c_0_43,c_0_44]),
    [final]).

cnf(c_0_55,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_56,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X4,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_57,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34])]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_21])]),
    [final]).

cnf(c_0_60,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( epred1_3(esk2_0,X1,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_34]),c_0_49]),c_0_22])]),
    [final]).

cnf(c_0_62,plain,
    ( esk4_4(esk1_0,X1,X2,X3) = esk4_4(esk1_0,X4,X5,X6)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | r1_yellow_0(esk1_0,k2_tarski(X4,X5))
    | ~ epred1_3(X5,X4,esk1_0)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X4,X5,X6))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X4,X5,X6),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X5,X6)
    | ~ r1_orders_2(esk1_0,X4,X6)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X6,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_49]),c_0_22])]),c_0_51]),
    [final]).

cnf(c_0_63,plain,
    ( esk4_4(esk1_0,X1,X2,X3) = esk4_4(esk1_0,X4,X5,X6)
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | r1_yellow_0(esk1_0,k2_tarski(X4,X5))
    | ~ epred1_3(X5,X4,esk1_0)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X4,X5,X6))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X4,X5,X6),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X5,X6)
    | ~ r1_orders_2(esk1_0,X4,X6)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X6,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_49]),c_0_22])]),c_0_53]),
    [final]).

cnf(c_0_64,plain,
    ( esk4_4(esk1_0,X1,X2,X3) = esk4_4(esk1_0,X4,X5,X6)
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | X6 = k10_lattice3(esk1_0,X4,X5)
    | ~ epred1_3(X5,X4,esk1_0)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X4,X5,X6))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X4,X5,X6),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X5,X6)
    | ~ r1_orders_2(esk1_0,X4,X6)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X6,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_49]),c_0_22])]),c_0_53]),
    [final]).

cnf(c_0_65,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r3_orders_2(X1,X4,esk4_4(X1,X2,X3,X5))
    | v2_struct_0(X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X4,esk4_4(X1,X2,X3,X5))
    | ~ r1_orders_2(X1,X3,X5)
    | ~ r1_orders_2(X1,X2,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_16]),
    [final]).

cnf(c_0_66,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r3_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))
    | v2_struct_0(X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_25]),
    [final]).

cnf(c_0_67,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( k10_lattice3(esk1_0,esk2_0,X1) = esk2_0
    | ~ epred1_3(X1,esk2_0,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_34]),c_0_58])]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | epred1_3(esk4_4(esk1_0,X2,X3,X1),esk2_0,esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_49]),c_0_22])]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k10_lattice3(esk1_0,esk3_0,X1) = esk3_0
    | ~ epred1_3(X1,esk3_0,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_21]),c_0_59])]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | epred1_3(esk4_4(esk1_0,X2,X3,X1),esk3_0,esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_49]),c_0_22])]),
    [final]).

cnf(c_0_72,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,X3,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_60]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( epred1_3(esk4_4(esk1_0,X1,X2,X3),esk2_0,esk1_0)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_34]),c_0_49]),c_0_22])]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( epred1_3(esk4_4(esk1_0,X1,X2,X3),esk3_0,esk1_0)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_49]),c_0_22])]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( epred1_3(esk3_0,X1,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_21]),c_0_49]),c_0_22])]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_34]),c_0_22]),c_0_23])]),c_0_24]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( k10_lattice3(esk1_0,X1,esk2_0) = esk2_0
    | ~ epred1_3(esk2_0,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_34]),c_0_58])]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( epred1_3(esk2_0,esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_21]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_81,plain,
    ( r1_orders_2(X2,X5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k10_lattice3(X2,X3,X4)
    | ~ r1_yellow_0(X2,k2_tarski(X3,X4))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_82,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X4,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_83,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X4,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_84,plain,
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
    inference(spm,[status(thm)],[c_0_32,c_0_27]),
    [final]).

cnf(c_0_85,plain,
    ( esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5) = esk4_4(esk1_0,X1,X2,X3)
    | r1_yellow_0(esk1_0,k2_tarski(esk4_4(esk1_0,X1,X2,X3),X4))
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X4,esk4_4(esk1_0,X1,X2,X3),esk1_0)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),X5)
    | ~ r1_orders_2(esk1_0,X4,X5)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X5,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_57]),
    [final]).

cnf(c_0_86,plain,
    ( esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5) = esk4_4(esk1_0,X2,X3,X4)
    | r1_yellow_0(esk1_0,k2_tarski(X1,esk4_4(esk1_0,X2,X3,X4)))
    | r1_yellow_0(esk1_0,k2_tarski(X2,X3))
    | ~ epred1_3(esk4_4(esk1_0,X2,X3,X4),X1,esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5),esk4_4(esk1_0,X2,X3,X4))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X4),X5)
    | ~ r1_orders_2(esk1_0,X1,X5)
    | ~ r1_orders_2(esk1_0,X3,X4)
    | ~ r1_orders_2(esk1_0,X2,X4)
    | ~ m1_subset_1(X5,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_60]),
    [final]).

cnf(c_0_87,plain,
    ( esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5) = esk4_4(esk1_0,X1,X2,X3)
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | r1_yellow_0(esk1_0,k2_tarski(esk4_4(esk1_0,X1,X2,X3),X4))
    | ~ epred1_3(X4,esk4_4(esk1_0,X1,X2,X3),esk1_0)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),X5)
    | ~ r1_orders_2(esk1_0,X4,X5)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X5,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57]),
    [final]).

cnf(c_0_88,plain,
    ( esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5) = esk4_4(esk1_0,X2,X3,X4)
    | X4 = k10_lattice3(esk1_0,X2,X3)
    | r1_yellow_0(esk1_0,k2_tarski(X1,esk4_4(esk1_0,X2,X3,X4)))
    | ~ epred1_3(esk4_4(esk1_0,X2,X3,X4),X1,esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5),esk4_4(esk1_0,X2,X3,X4))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X4),X5)
    | ~ r1_orders_2(esk1_0,X1,X5)
    | ~ r1_orders_2(esk1_0,X3,X4)
    | ~ r1_orders_2(esk1_0,X2,X4)
    | ~ m1_subset_1(X5,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_60]),
    [final]).

cnf(c_0_89,plain,
    ( esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5) = esk4_4(esk1_0,X1,X2,X3)
    | X5 = k10_lattice3(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4)
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | ~ epred1_3(X4,esk4_4(esk1_0,X1,X2,X3),esk1_0)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5),esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),X5)
    | ~ r1_orders_2(esk1_0,X4,X5)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X5,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_11]),
    [final]).

cnf(c_0_90,plain,
    ( esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5) = esk4_4(esk1_0,X2,X3,X4)
    | X5 = k10_lattice3(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4))
    | X4 = k10_lattice3(esk1_0,X2,X3)
    | ~ epred1_3(esk4_4(esk1_0,X2,X3,X4),X1,esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5),esk4_4(esk1_0,X2,X3,X4))
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X4),X5)
    | ~ r1_orders_2(esk1_0,X1,X5)
    | ~ r1_orders_2(esk1_0,X3,X4)
    | ~ r1_orders_2(esk1_0,X2,X4)
    | ~ m1_subset_1(X5,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_10]),
    [final]).

cnf(c_0_91,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_yellow_0(X1,k2_tarski(X4,X5))
    | r3_orders_2(X1,esk4_4(X1,X2,X3,X6),esk4_4(X1,X4,X5,X7))
    | v2_struct_0(X1)
    | ~ epred1_3(X5,X4,X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X6),esk4_4(X1,X4,X5,X7))
    | ~ r1_orders_2(X1,X5,X7)
    | ~ r1_orders_2(X1,X4,X7)
    | ~ r1_orders_2(X1,X3,X6)
    | ~ r1_orders_2(X1,X2,X6)
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_16]),
    [final]).

cnf(c_0_92,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_yellow_0(X2,k2_tarski(X5,X6))
    | r3_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X5,X6,X7))
    | v2_struct_0(X2)
    | ~ epred1_3(X6,X5,X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X5,X6,X7))
    | ~ r1_orders_2(X2,X6,X7)
    | ~ r1_orders_2(X2,X5,X7)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X7,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_25]),
    [final]).

cnf(c_0_93,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | X5 = k10_lattice3(X2,X6,X7)
    | r3_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X6,X7,X5))
    | v2_struct_0(X2)
    | ~ epred1_3(X7,X6,X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X6,X7,X5))
    | ~ r1_orders_2(X2,X7,X5)
    | ~ r1_orders_2(X2,X6,X5)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_25]),
    [final]).

cnf(c_0_94,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_yellow_0(X2,k2_tarski(X5,X6))
    | r3_orders_2(X2,esk4_4(X2,X5,X6,X7),esk4_4(X2,X3,X4,X1))
    | v2_struct_0(X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ epred1_3(X6,X5,X2)
    | ~ r1_orders_2(X2,esk4_4(X2,X5,X6,X7),esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X6,X7)
    | ~ r1_orders_2(X2,X5,X7)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X7,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_16]),
    [final]).

cnf(c_0_95,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_yellow_0(X2,k2_tarski(esk4_4(X2,X3,X4,X1),X5))
    | ~ epred1_3(X5,esk4_4(X2,X3,X4,X1),X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_25]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( esk4_4(esk1_0,X1,X2,X3) = esk2_0
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_32]),c_0_53]),c_0_69]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( esk4_4(esk1_0,X1,X2,X3) = esk3_0
    | X3 = k10_lattice3(esk1_0,X1,X2)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_32]),c_0_53]),c_0_71]),
    [final]).

cnf(c_0_98,plain,
    ( r1_yellow_0(X1,k2_tarski(esk4_4(X1,X2,X3,X4),X5))
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_16]),
    [final]).

cnf(c_0_99,plain,
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
    inference(spm,[status(thm)],[c_0_33,c_0_16]),
    [final]).

cnf(c_0_100,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_yellow_0(X2,k2_tarski(X5,esk4_4(X2,X3,X4,X1)))
    | ~ epred1_3(esk4_4(X2,X3,X4,X1),X5,X2)
    | ~ epred1_3(X4,X3,X2)
    | ~ r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_25]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( esk4_4(esk1_0,X1,X2,X3) = esk2_0
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_26]),c_0_51]),c_0_73]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( esk4_4(esk1_0,X1,X2,X3) = esk3_0
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_26]),c_0_51]),c_0_74]),
    [final]).

cnf(c_0_103,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,esk4_4(X1,X3,X4,X5)))
    | r1_yellow_0(X1,k2_tarski(X3,X4))
    | ~ epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)
    | ~ epred1_3(X4,X3,X1)
    | ~ r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X4,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_16]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | r3_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_34]),c_0_22]),c_0_23])]),c_0_24]),
    [final]).

cnf(c_0_105,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | r3_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),
    [final]).

cnf(c_0_106,plain,
    ( epred1_3(esk2_0,esk4_4(esk1_0,X1,X2,X3),esk1_0)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_16]),
    [final]).

cnf(c_0_107,plain,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | epred1_3(esk2_0,esk4_4(esk1_0,X2,X3,X1),esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_25]),
    [final]).

cnf(c_0_108,plain,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | epred1_3(esk3_0,esk4_4(esk1_0,X2,X3,X1),esk1_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_25]),
    [final]).

cnf(c_0_109,plain,
    ( epred1_3(esk3_0,esk4_4(esk1_0,X1,X2,X3),esk1_0)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_16]),
    [final]).

cnf(c_0_110,plain,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | r3_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_16]),
    [final]).

cnf(c_0_111,plain,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | r3_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)
    | ~ epred1_3(X2,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_16]),
    [final]).

cnf(c_0_112,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | r3_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X2,X3,X1))
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X2,X3,X1))
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_34]),c_0_22]),c_0_23])]),c_0_24]),
    [final]).

cnf(c_0_113,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(esk2_0,X1))
    | ~ epred1_3(X1,esk2_0,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_34]),c_0_58])]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(esk3_0,X1))
    | ~ epred1_3(X1,esk3_0,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_21]),c_0_59])]),
    [final]).

cnf(c_0_115,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | r3_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X2,X3,X1))
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X2,X3,X1))
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),
    [final]).

cnf(c_0_116,plain,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | r3_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk2_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk2_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_25]),
    [final]).

cnf(c_0_117,plain,
    ( X1 = k10_lattice3(esk1_0,X2,X3)
    | r3_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk3_0)
    | ~ epred1_3(X3,X2,esk1_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk3_0)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_25]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_70]),c_0_79])]),c_0_80]),
    [final]).

cnf(c_0_119,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,esk2_0))
    | ~ epred1_3(esk2_0,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_34]),c_0_58])]),
    [final]).

cnf(c_0_120,negated_conjecture,
    ( r1_yellow_0(esk1_0,k2_tarski(X1,esk3_0))
    | ~ epred1_3(esk3_0,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_21]),c_0_59])]),
    [final]).

cnf(c_0_121,negated_conjecture,
    ( k10_lattice3(esk1_0,X1,esk3_0) = esk3_0
    | ~ epred1_3(esk3_0,X1,esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_21]),c_0_59])]),
    [final]).

cnf(c_0_122,negated_conjecture,
    ( r3_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_21]),
    [final]).

cnf(c_0_123,negated_conjecture,
    ( r3_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_34]),
    [final]).

cnf(c_0_124,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_81]),
    [final]).

cnf(c_0_125,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ epred1_3(X3,X2,X1)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_82]),
    [final]).

cnf(c_0_126,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ epred1_3(X2,X3,X1)
    | ~ r1_yellow_0(X1,k2_tarski(X3,X2))
    | ~ m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_83]),
    [final]).

cnf(c_0_127,negated_conjecture,
    ( epred1_3(esk2_0,esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_34]),
    [final]).

cnf(c_0_128,negated_conjecture,
    ( epred1_3(esk3_0,esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_34]),
    [final]).

cnf(c_0_129,negated_conjecture,
    ( epred1_3(esk3_0,esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_21]),
    [final]).

cnf(c_0_130,negated_conjecture,
    ( k6_waybel_0(esk1_0,esk2_0) = k6_waybel_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:49:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # No proof found!
% 0.20/0.41  # SZS status CounterSatisfiable
% 0.20/0.41  # SZS output start Saturation
% 0.20/0.41  fof(t18_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3)))=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))&(((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))=>(X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_0)).
% 0.20/0.41  fof(t20_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k6_waybel_0(X1,X2)=k6_waybel_0(X1,X3)=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_waybel_0)).
% 0.20/0.41  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.20/0.41  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.41  fof(c_0_4, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3)))=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))&(((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))=>(X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3))))))), introduced(definition)).
% 0.20/0.41  fof(c_0_5, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3)))=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))&(((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))=>(X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3))))))), inference(split_equiv,[status(thm)],[c_0_4])).
% 0.20/0.41  fof(c_0_6, plain, ![X18, X19, X20, X21, X22]:((((r1_orders_2(X18,X19,X21)|(X21!=k10_lattice3(X18,X19,X20)|~r1_yellow_0(X18,k2_tarski(X19,X20)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18))&(r1_orders_2(X18,X20,X21)|(X21!=k10_lattice3(X18,X19,X20)|~r1_yellow_0(X18,k2_tarski(X19,X20)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18)))&(~m1_subset_1(X22,u1_struct_0(X18))|(~r1_orders_2(X18,X19,X22)|~r1_orders_2(X18,X20,X22)|r1_orders_2(X18,X21,X22))|(X21!=k10_lattice3(X18,X19,X20)|~r1_yellow_0(X18,k2_tarski(X19,X20)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18)))&(((X21=k10_lattice3(X18,X19,X20)|(m1_subset_1(esk4_4(X18,X19,X20,X21),u1_struct_0(X18))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18))&(r1_yellow_0(X18,k2_tarski(X19,X20))|(m1_subset_1(esk4_4(X18,X19,X20,X21),u1_struct_0(X18))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18)))&((((X21=k10_lattice3(X18,X19,X20)|(r1_orders_2(X18,X19,esk4_4(X18,X19,X20,X21))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18))&(r1_yellow_0(X18,k2_tarski(X19,X20))|(r1_orders_2(X18,X19,esk4_4(X18,X19,X20,X21))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18)))&((X21=k10_lattice3(X18,X19,X20)|(r1_orders_2(X18,X20,esk4_4(X18,X19,X20,X21))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18))&(r1_yellow_0(X18,k2_tarski(X19,X20))|(r1_orders_2(X18,X20,esk4_4(X18,X19,X20,X21))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18))))&((X21=k10_lattice3(X18,X19,X20)|(~r1_orders_2(X18,X21,esk4_4(X18,X19,X20,X21))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18))&(r1_yellow_0(X18,k2_tarski(X19,X20))|(~r1_orders_2(X18,X21,esk4_4(X18,X19,X20,X21))|(~r1_orders_2(X18,X19,X21)|~r1_orders_2(X18,X20,X21)))|~m1_subset_1(X21,u1_struct_0(X18))|~epred1_3(X20,X19,X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).
% 0.20/0.41  fof(c_0_7, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>epred1_3(X3,X2,X1)))), inference(apply_def,[status(thm)],[t18_yellow_0, c_0_4])).
% 0.20/0.41  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k6_waybel_0(X1,X2)=k6_waybel_0(X1,X3)=>X2=X3))))), inference(assume_negation,[status(cth)],[t20_waybel_0])).
% 0.20/0.41  cnf(c_0_9, plain, (X1=k10_lattice3(X2,X3,X4)|~r1_orders_2(X2,X1,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.41  cnf(c_0_10, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X4,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.41  cnf(c_0_11, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X3,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.41  fof(c_0_12, plain, ![X12, X13, X14]:(~v5_orders_2(X12)|~l1_orders_2(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|epred1_3(X14,X13,X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.41  fof(c_0_13, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|r3_orders_2(X9,X10,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ((((~v2_struct_0(esk1_0)&v3_orders_2(esk1_0))&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(k6_waybel_0(esk1_0,esk2_0)=k6_waybel_0(esk1_0,esk3_0)&esk2_0!=esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.20/0.41  cnf(c_0_15, plain, (k10_lattice3(X1,X2,X3)=X3|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.20/0.41  cnf(c_0_16, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.41  cnf(c_0_17, plain, (k10_lattice3(X1,X2,X3)=X2|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X2)|~r1_orders_2(X1,X2,X2)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_9, c_0_11]), ['final']).
% 0.20/0.41  cnf(c_0_18, plain, (epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.20/0.41  fof(c_0_19, plain, ![X6, X7, X8]:((~r3_orders_2(X6,X7,X8)|r1_orders_2(X6,X7,X8)|(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))&(~r1_orders_2(X6,X7,X8)|r3_orders_2(X6,X7,X8)|(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.41  cnf(c_0_20, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.41  cnf(c_0_25, plain, (X1=k10_lattice3(X2,X3,X4)|m1_subset_1(esk4_4(X2,X3,X4,X1),u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.41  cnf(c_0_26, plain, (k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5))=esk4_4(X1,X3,X4,X5)|r1_yellow_0(X1,k2_tarski(X3,X4))|~epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)|~epred1_3(X4,X3,X1)|~r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X4,X5)|~r1_orders_2(X1,X3,X5)|~m1_subset_1(X5,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_27, plain, (k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5)=esk4_4(X1,X2,X3,X4)|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_17, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_28, plain, (epred1_3(esk4_4(X1,X2,X3,X4),X5,X1)|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_29, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (r3_orders_2(esk1_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_31, plain, (k10_lattice3(X1,esk4_4(X1,X2,X3,X4),X5)=esk4_4(X1,X2,X3,X4)|X4=k10_lattice3(X1,X2,X3)|~epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_17, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_32, plain, (k10_lattice3(X1,X2,esk4_4(X1,X3,X4,X5))=esk4_4(X1,X3,X4,X5)|X5=k10_lattice3(X1,X3,X4)|~epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)|~epred1_3(X4,X3,X1)|~r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X4,X5)|~r1_orders_2(X1,X3,X5)|~m1_subset_1(X5,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_15, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_33, plain, (X1=k10_lattice3(X2,X3,X4)|epred1_3(esk4_4(X2,X3,X4,X1),X5,X2)|~epred1_3(X4,X3,X2)|~v5_orders_2(X2)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_18, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.41  cnf(c_0_35, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|r1_yellow_0(X1,k2_tarski(X2,X3))|r1_yellow_0(X1,k2_tarski(X5,X6))|~epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27]), ['final']).
% 0.20/0.41  cnf(c_0_36, plain, (epred1_3(esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7),X1)|r1_yellow_0(X1,k2_tarski(X5,X6))|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X3,X2,X1)|~epred1_3(X6,X5,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_37, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,X4,esk4_4(X1,X2,X3,X5))|v2_struct_0(X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X5)|~r1_orders_2(X1,X2,X5)|~r3_orders_2(X1,X4,esk4_4(X1,X2,X3,X5))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_29, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_38, plain, (r1_yellow_0(esk1_0,k2_tarski(X1,X2))|r3_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_30, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_39, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X4=k10_lattice3(X1,X2,X3)|r1_yellow_0(X1,k2_tarski(X5,X6))|~epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_31]), ['final']).
% 0.20/0.41  cnf(c_0_40, plain, (X1=k10_lattice3(X2,X3,X4)|epred1_3(esk4_4(X2,X5,X6,X7),esk4_4(X2,X3,X4,X1),X2)|r1_yellow_0(X2,k2_tarski(X5,X6))|~epred1_3(X6,X5,X2)|~epred1_3(X4,X3,X2)|~v5_orders_2(X2)|~r1_orders_2(X2,X6,X7)|~r1_orders_2(X2,X5,X7)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X7,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_28, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_41, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))|v2_struct_0(X2)|~epred1_3(X4,X3,X2)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~r3_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_29, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_42, plain, (X1=k10_lattice3(esk1_0,X2,X3)|r3_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk4_4(esk1_0,X2,X3,X1))|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_30, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_43, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X4=k10_lattice3(X1,X2,X3)|X7=k10_lattice3(X1,X5,X6)|~epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_32, c_0_31]), ['final']).
% 0.20/0.41  cnf(c_0_44, plain, (X1=k10_lattice3(X2,X3,X4)|X5=k10_lattice3(X2,X6,X7)|epred1_3(esk4_4(X2,X6,X7,X5),esk4_4(X2,X3,X4,X1),X2)|~epred1_3(X7,X6,X2)|~epred1_3(X4,X3,X2)|~v5_orders_2(X2)|~r1_orders_2(X2,X7,X5)|~r1_orders_2(X2,X6,X5)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_33, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk1_0,X1,esk2_0)|~r3_orders_2(esk1_0,X1,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_34]), c_0_22]), c_0_23])]), c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r3_orders_2(esk1_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_34]), ['final']).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk1_0,X1,esk3_0)|~r3_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_21]), c_0_22]), c_0_23])]), c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (r3_orders_2(esk1_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_21]), ['final']).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.41  cnf(c_0_50, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|r1_yellow_0(X1,k2_tarski(X5,X6))|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.20/0.41  cnf(c_0_51, plain, (r1_yellow_0(esk1_0,k2_tarski(X1,X2))|r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X1,X2,X3))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_22]), c_0_23])]), c_0_24]), c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_52, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X4=k10_lattice3(X1,X2,X3)|r1_yellow_0(X1,k2_tarski(X5,X6))|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40]), ['final']).
% 0.20/0.41  cnf(c_0_53, plain, (X1=k10_lattice3(esk1_0,X2,X3)|r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk4_4(esk1_0,X2,X3,X1))|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_22]), c_0_23])]), c_0_24]), c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_54, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X7=k10_lattice3(X1,X5,X6)|X4=k10_lattice3(X1,X2,X3)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44]), ['final']).
% 0.20/0.41  cnf(c_0_55, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.20/0.41  cnf(c_0_56, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|~r1_orders_2(X1,X4,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.41  cnf(c_0_57, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,X2,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (r1_orders_2(esk1_0,esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_34])]), ['final']).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk1_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_21])]), ['final']).
% 0.20/0.41  cnf(c_0_60, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,X3,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (epred1_3(esk2_0,X1,esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_34]), c_0_49]), c_0_22])]), ['final']).
% 0.20/0.41  cnf(c_0_62, plain, (esk4_4(esk1_0,X1,X2,X3)=esk4_4(esk1_0,X4,X5,X6)|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|r1_yellow_0(esk1_0,k2_tarski(X4,X5))|~epred1_3(X5,X4,esk1_0)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X4,X5,X6))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X4,X5,X6),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X5,X6)|~r1_orders_2(esk1_0,X4,X6)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X6,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_49]), c_0_22])]), c_0_51]), ['final']).
% 0.20/0.41  cnf(c_0_63, plain, (esk4_4(esk1_0,X1,X2,X3)=esk4_4(esk1_0,X4,X5,X6)|X3=k10_lattice3(esk1_0,X1,X2)|r1_yellow_0(esk1_0,k2_tarski(X4,X5))|~epred1_3(X5,X4,esk1_0)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X4,X5,X6))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X4,X5,X6),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X5,X6)|~r1_orders_2(esk1_0,X4,X6)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X6,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_51]), c_0_49]), c_0_22])]), c_0_53]), ['final']).
% 0.20/0.41  cnf(c_0_64, plain, (esk4_4(esk1_0,X1,X2,X3)=esk4_4(esk1_0,X4,X5,X6)|X3=k10_lattice3(esk1_0,X1,X2)|X6=k10_lattice3(esk1_0,X4,X5)|~epred1_3(X5,X4,esk1_0)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk4_4(esk1_0,X4,X5,X6))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X4,X5,X6),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X5,X6)|~r1_orders_2(esk1_0,X4,X6)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X6,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_53]), c_0_49]), c_0_22])]), c_0_53]), ['final']).
% 0.20/0.41  cnf(c_0_65, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|r3_orders_2(X1,X4,esk4_4(X1,X2,X3,X5))|v2_struct_0(X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X4,esk4_4(X1,X2,X3,X5))|~r1_orders_2(X1,X3,X5)|~r1_orders_2(X1,X2,X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_55, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_66, plain, (X1=k10_lattice3(X2,X3,X4)|r3_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))|v2_struct_0(X2)|~epred1_3(X4,X3,X2)|~r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_55, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_67, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X2)|~r1_orders_2(X1,X2,X2)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57]), ['final']).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (k10_lattice3(esk1_0,esk2_0,X1)=esk2_0|~epred1_3(X1,esk2_0,esk1_0)|~r1_orders_2(esk1_0,X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_34]), c_0_58])]), ['final']).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (X1=k10_lattice3(esk1_0,X2,X3)|epred1_3(esk4_4(esk1_0,X2,X3,X1),esk2_0,esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_49]), c_0_22])]), ['final']).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (k10_lattice3(esk1_0,esk3_0,X1)=esk3_0|~epred1_3(X1,esk3_0,esk1_0)|~r1_orders_2(esk1_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_21]), c_0_59])]), ['final']).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (X1=k10_lattice3(esk1_0,X2,X3)|epred1_3(esk4_4(esk1_0,X2,X3,X1),esk3_0,esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_21]), c_0_49]), c_0_22])]), ['final']).
% 0.20/0.41  cnf(c_0_72, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,X3,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_60]), ['final']).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (epred1_3(esk4_4(esk1_0,X1,X2,X3),esk2_0,esk1_0)|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_34]), c_0_49]), c_0_22])]), ['final']).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (epred1_3(esk4_4(esk1_0,X1,X2,X3),esk3_0,esk1_0)|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_21]), c_0_49]), c_0_22])]), ['final']).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (epred1_3(esk3_0,X1,esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_21]), c_0_49]), c_0_22])]), ['final']).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (r3_orders_2(esk1_0,X1,esk2_0)|~r1_orders_2(esk1_0,X1,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_34]), c_0_22]), c_0_23])]), c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (r3_orders_2(esk1_0,X1,esk3_0)|~r1_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_21]), c_0_22]), c_0_23])]), c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (k10_lattice3(esk1_0,X1,esk2_0)=esk2_0|~epred1_3(esk2_0,X1,esk1_0)|~r1_orders_2(esk1_0,X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_34]), c_0_58])]), ['final']).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (epred1_3(esk2_0,esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_61, c_0_21]), ['final']).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.41  cnf(c_0_81, plain, (r1_orders_2(X2,X5,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|X5!=k10_lattice3(X2,X3,X4)|~r1_yellow_0(X2,k2_tarski(X3,X4))|~m1_subset_1(X5,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_82, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X2,X4)|~r1_yellow_0(X1,k2_tarski(X2,X4))|~m1_subset_1(X3,u1_struct_0(X1))|~epred1_3(X4,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_83, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X4,X2)|~r1_yellow_0(X1,k2_tarski(X4,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~epred1_3(X2,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_84, plain, (esk4_4(X1,X2,X3,X4)=esk4_4(X1,X5,X6,X7)|X7=k10_lattice3(X1,X5,X6)|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X6,X5,X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X5,X6,X7))|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,esk4_4(X1,X5,X6,X7),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X6,X7)|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_32, c_0_27]), ['final']).
% 0.20/0.41  cnf(c_0_85, plain, (esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5)=esk4_4(esk1_0,X1,X2,X3)|r1_yellow_0(esk1_0,k2_tarski(esk4_4(esk1_0,X1,X2,X3),X4))|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X4,esk4_4(esk1_0,X1,X2,X3),esk1_0)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),X5)|~r1_orders_2(esk1_0,X4,X5)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X5,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_62, c_0_57]), ['final']).
% 0.20/0.41  cnf(c_0_86, plain, (esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5)=esk4_4(esk1_0,X2,X3,X4)|r1_yellow_0(esk1_0,k2_tarski(X1,esk4_4(esk1_0,X2,X3,X4)))|r1_yellow_0(esk1_0,k2_tarski(X2,X3))|~epred1_3(esk4_4(esk1_0,X2,X3,X4),X1,esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5),esk4_4(esk1_0,X2,X3,X4))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X4),X5)|~r1_orders_2(esk1_0,X1,X5)|~r1_orders_2(esk1_0,X3,X4)|~r1_orders_2(esk1_0,X2,X4)|~m1_subset_1(X5,u1_struct_0(esk1_0))|~m1_subset_1(X4,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_62, c_0_60]), ['final']).
% 0.20/0.41  cnf(c_0_87, plain, (esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5)=esk4_4(esk1_0,X1,X2,X3)|X3=k10_lattice3(esk1_0,X1,X2)|r1_yellow_0(esk1_0,k2_tarski(esk4_4(esk1_0,X1,X2,X3),X4))|~epred1_3(X4,esk4_4(esk1_0,X1,X2,X3),esk1_0)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),X5)|~r1_orders_2(esk1_0,X4,X5)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X5,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_63, c_0_57]), ['final']).
% 0.20/0.41  cnf(c_0_88, plain, (esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5)=esk4_4(esk1_0,X2,X3,X4)|X4=k10_lattice3(esk1_0,X2,X3)|r1_yellow_0(esk1_0,k2_tarski(X1,esk4_4(esk1_0,X2,X3,X4)))|~epred1_3(esk4_4(esk1_0,X2,X3,X4),X1,esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5),esk4_4(esk1_0,X2,X3,X4))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X4),X5)|~r1_orders_2(esk1_0,X1,X5)|~r1_orders_2(esk1_0,X3,X4)|~r1_orders_2(esk1_0,X2,X4)|~m1_subset_1(X5,u1_struct_0(esk1_0))|~m1_subset_1(X4,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_63, c_0_60]), ['final']).
% 0.20/0.41  cnf(c_0_89, plain, (esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5)=esk4_4(esk1_0,X1,X2,X3)|X5=k10_lattice3(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4)|X3=k10_lattice3(esk1_0,X1,X2)|~epred1_3(X4,esk4_4(esk1_0,X1,X2,X3),esk1_0)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,esk4_4(esk1_0,X1,X2,X3),X4,X5),esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),X5)|~r1_orders_2(esk1_0,X4,X5)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X5,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_64, c_0_11]), ['final']).
% 0.20/0.41  cnf(c_0_90, plain, (esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5)=esk4_4(esk1_0,X2,X3,X4)|X5=k10_lattice3(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4))|X4=k10_lattice3(esk1_0,X2,X3)|~epred1_3(esk4_4(esk1_0,X2,X3,X4),X1,esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,esk4_4(esk1_0,X2,X3,X4),X5),esk4_4(esk1_0,X2,X3,X4))|~r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X4),X5)|~r1_orders_2(esk1_0,X1,X5)|~r1_orders_2(esk1_0,X3,X4)|~r1_orders_2(esk1_0,X2,X4)|~m1_subset_1(X5,u1_struct_0(esk1_0))|~m1_subset_1(X4,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_64, c_0_10]), ['final']).
% 0.20/0.41  cnf(c_0_91, plain, (r1_yellow_0(X1,k2_tarski(X2,X3))|r1_yellow_0(X1,k2_tarski(X4,X5))|r3_orders_2(X1,esk4_4(X1,X2,X3,X6),esk4_4(X1,X4,X5,X7))|v2_struct_0(X1)|~epred1_3(X5,X4,X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X6),esk4_4(X1,X4,X5,X7))|~r1_orders_2(X1,X5,X7)|~r1_orders_2(X1,X4,X7)|~r1_orders_2(X1,X3,X6)|~r1_orders_2(X1,X2,X6)|~m1_subset_1(X7,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_65, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_92, plain, (X1=k10_lattice3(X2,X3,X4)|r1_yellow_0(X2,k2_tarski(X5,X6))|r3_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X5,X6,X7))|v2_struct_0(X2)|~epred1_3(X6,X5,X2)|~epred1_3(X4,X3,X2)|~r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X5,X6,X7))|~r1_orders_2(X2,X6,X7)|~r1_orders_2(X2,X5,X7)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X7,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_65, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_93, plain, (X1=k10_lattice3(X2,X3,X4)|X5=k10_lattice3(X2,X6,X7)|r3_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X6,X7,X5))|v2_struct_0(X2)|~epred1_3(X7,X6,X2)|~epred1_3(X4,X3,X2)|~r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X6,X7,X5))|~r1_orders_2(X2,X7,X5)|~r1_orders_2(X2,X6,X5)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_66, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_94, plain, (X1=k10_lattice3(X2,X3,X4)|r1_yellow_0(X2,k2_tarski(X5,X6))|r3_orders_2(X2,esk4_4(X2,X5,X6,X7),esk4_4(X2,X3,X4,X1))|v2_struct_0(X2)|~epred1_3(X4,X3,X2)|~epred1_3(X6,X5,X2)|~r1_orders_2(X2,esk4_4(X2,X5,X6,X7),esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X6,X7)|~r1_orders_2(X2,X5,X7)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X7,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_66, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_95, plain, (X1=k10_lattice3(X2,X3,X4)|r1_yellow_0(X2,k2_tarski(esk4_4(X2,X3,X4,X1),X5))|~epred1_3(X5,esk4_4(X2,X3,X4,X1),X2)|~epred1_3(X4,X3,X2)|~r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_67, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (esk4_4(esk1_0,X1,X2,X3)=esk2_0|X3=k10_lattice3(esk1_0,X1,X2)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)|~r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_32]), c_0_53]), c_0_69]), ['final']).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (esk4_4(esk1_0,X1,X2,X3)=esk3_0|X3=k10_lattice3(esk1_0,X1,X2)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)|~r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_32]), c_0_53]), c_0_71]), ['final']).
% 0.20/0.41  cnf(c_0_98, plain, (r1_yellow_0(X1,k2_tarski(esk4_4(X1,X2,X3,X4),X5))|r1_yellow_0(X1,k2_tarski(X2,X3))|~epred1_3(X5,esk4_4(X1,X2,X3,X4),X1)|~epred1_3(X3,X2,X1)|~r1_orders_2(X1,esk4_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X4))|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_67, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_99, plain, (X1=k10_lattice3(X2,X3,X4)|epred1_3(esk4_4(X2,X3,X4,X1),esk4_4(X2,X5,X6,X7),X2)|r1_yellow_0(X2,k2_tarski(X5,X6))|~epred1_3(X4,X3,X2)|~epred1_3(X6,X5,X2)|~v5_orders_2(X2)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X6,X7)|~r1_orders_2(X2,X5,X7)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X7,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_33, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_100, plain, (X1=k10_lattice3(X2,X3,X4)|r1_yellow_0(X2,k2_tarski(X5,esk4_4(X2,X3,X4,X1)))|~epred1_3(esk4_4(X2,X3,X4,X1),X5,X2)|~epred1_3(X4,X3,X2)|~r1_orders_2(X2,esk4_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X5,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_72, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_101, negated_conjecture, (esk4_4(esk1_0,X1,X2,X3)=esk2_0|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)|~r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_26]), c_0_51]), c_0_73]), ['final']).
% 0.20/0.41  cnf(c_0_102, negated_conjecture, (esk4_4(esk1_0,X1,X2,X3)=esk3_0|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)|~r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_26]), c_0_51]), c_0_74]), ['final']).
% 0.20/0.41  cnf(c_0_103, plain, (r1_yellow_0(X1,k2_tarski(X2,esk4_4(X1,X3,X4,X5)))|r1_yellow_0(X1,k2_tarski(X3,X4))|~epred1_3(esk4_4(X1,X3,X4,X5),X2,X1)|~epred1_3(X4,X3,X1)|~r1_orders_2(X1,esk4_4(X1,X3,X4,X5),esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X2,esk4_4(X1,X3,X4,X5))|~r1_orders_2(X1,X4,X5)|~r1_orders_2(X1,X3,X5)|~m1_subset_1(X5,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_72, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_104, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(X1,X2))|r3_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_34]), c_0_22]), c_0_23])]), c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_105, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(X1,X2))|r3_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X1,X2,X3))|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_21]), c_0_22]), c_0_23])]), c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_106, plain, (epred1_3(esk2_0,esk4_4(esk1_0,X1,X2,X3),esk1_0)|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_61, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_107, plain, (X1=k10_lattice3(esk1_0,X2,X3)|epred1_3(esk2_0,esk4_4(esk1_0,X2,X3,X1),esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_61, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_108, plain, (X1=k10_lattice3(esk1_0,X2,X3)|epred1_3(esk3_0,esk4_4(esk1_0,X2,X3,X1),esk1_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_75, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_109, plain, (epred1_3(esk3_0,esk4_4(esk1_0,X1,X2,X3),esk1_0)|r1_yellow_0(esk1_0,k2_tarski(X1,X2))|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_75, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_110, plain, (r1_yellow_0(esk1_0,k2_tarski(X1,X2))|r3_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk2_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_76, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_111, plain, (r1_yellow_0(esk1_0,k2_tarski(X1,X2))|r3_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)|~epred1_3(X2,X1,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X1,X2,X3),esk3_0)|~r1_orders_2(esk1_0,X2,X3)|~r1_orders_2(esk1_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_77, c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_112, negated_conjecture, (X1=k10_lattice3(esk1_0,X2,X3)|r3_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X2,X3,X1))|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,esk2_0,esk4_4(esk1_0,X2,X3,X1))|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_34]), c_0_22]), c_0_23])]), c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_113, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(esk2_0,X1))|~epred1_3(X1,esk2_0,esk1_0)|~r1_orders_2(esk1_0,X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_34]), c_0_58])]), ['final']).
% 0.20/0.41  cnf(c_0_114, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(esk3_0,X1))|~epred1_3(X1,esk3_0,esk1_0)|~r1_orders_2(esk1_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_21]), c_0_59])]), ['final']).
% 0.20/0.41  cnf(c_0_115, negated_conjecture, (X1=k10_lattice3(esk1_0,X2,X3)|r3_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X2,X3,X1))|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X2,X3,X1))|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_21]), c_0_22]), c_0_23])]), c_0_24]), ['final']).
% 0.20/0.41  cnf(c_0_116, plain, (X1=k10_lattice3(esk1_0,X2,X3)|r3_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk2_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk2_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_76, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_117, plain, (X1=k10_lattice3(esk1_0,X2,X3)|r3_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk3_0)|~epred1_3(X3,X2,esk1_0)|~r1_orders_2(esk1_0,esk4_4(esk1_0,X2,X3,X1),esk3_0)|~r1_orders_2(esk1_0,X3,X1)|~r1_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_77, c_0_25]), ['final']).
% 0.20/0.41  cnf(c_0_118, negated_conjecture, (~r1_orders_2(esk1_0,esk3_0,esk2_0)|~r1_orders_2(esk1_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_70]), c_0_79])]), c_0_80]), ['final']).
% 0.20/0.41  cnf(c_0_119, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(X1,esk2_0))|~epred1_3(esk2_0,X1,esk1_0)|~r1_orders_2(esk1_0,X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_34]), c_0_58])]), ['final']).
% 0.20/0.41  cnf(c_0_120, negated_conjecture, (r1_yellow_0(esk1_0,k2_tarski(X1,esk3_0))|~epred1_3(esk3_0,X1,esk1_0)|~r1_orders_2(esk1_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_21]), c_0_59])]), ['final']).
% 0.20/0.41  cnf(c_0_121, negated_conjecture, (k10_lattice3(esk1_0,X1,esk3_0)=esk3_0|~epred1_3(esk3_0,X1,esk1_0)|~r1_orders_2(esk1_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_21]), c_0_59])]), ['final']).
% 0.20/0.41  cnf(c_0_122, negated_conjecture, (r3_orders_2(esk1_0,esk3_0,esk2_0)|~r1_orders_2(esk1_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_76, c_0_21]), ['final']).
% 0.20/0.41  cnf(c_0_123, negated_conjecture, (r3_orders_2(esk1_0,esk2_0,esk3_0)|~r1_orders_2(esk1_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_77, c_0_34]), ['final']).
% 0.20/0.41  cnf(c_0_124, plain, (r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)|~epred1_3(X3,X2,X1)|~r1_yellow_0(X1,k2_tarski(X2,X3))|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_81]), ['final']).
% 0.20/0.41  cnf(c_0_125, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))|~epred1_3(X3,X2,X1)|~r1_yellow_0(X1,k2_tarski(X2,X3))|~m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), inference(er,[status(thm)],[c_0_82]), ['final']).
% 0.20/0.41  cnf(c_0_126, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))|~epred1_3(X2,X3,X1)|~r1_yellow_0(X1,k2_tarski(X3,X2))|~m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1))), inference(er,[status(thm)],[c_0_83]), ['final']).
% 0.20/0.41  cnf(c_0_127, negated_conjecture, (epred1_3(esk2_0,esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_61, c_0_34]), ['final']).
% 0.20/0.41  cnf(c_0_128, negated_conjecture, (epred1_3(esk3_0,esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_75, c_0_34]), ['final']).
% 0.20/0.41  cnf(c_0_129, negated_conjecture, (epred1_3(esk3_0,esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_75, c_0_21]), ['final']).
% 0.20/0.41  cnf(c_0_130, negated_conjecture, (k6_waybel_0(esk1_0,esk2_0)=k6_waybel_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.41  # SZS output end Saturation
% 0.20/0.41  # Proof object total steps             : 131
% 0.20/0.41  # Proof object clause steps            : 118
% 0.20/0.41  # Proof object formula steps           : 13
% 0.20/0.41  # Proof object conjectures             : 49
% 0.20/0.41  # Proof object clause conjectures      : 46
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 23
% 0.20/0.41  # Proof object initial formulas used   : 4
% 0.20/0.41  # Proof object generating inferences   : 92
% 0.20/0.41  # Proof object simplifying inferences  : 110
% 0.20/0.41  # Parsed axioms                        : 4
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 23
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 23
% 0.20/0.41  # Processed clauses                    : 177
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 36
% 0.20/0.41  # ...remaining for further processing  : 141
% 0.20/0.41  # Other redundant clauses eliminated   : 3
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 0
% 0.20/0.41  # Generated clauses                    : 179
% 0.20/0.41  # ...of the previous two non-trivial   : 131
% 0.20/0.41  # Contextual simplify-reflections      : 13
% 0.20/0.41  # Paramodulations                      : 176
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
% 0.20/0.41  # Current number of processed clauses  : 115
% 0.20/0.41  #    Positive orientable unit clauses  : 14
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 2
% 0.20/0.41  #    Non-unit-clauses                  : 99
% 0.20/0.41  # Current number of unprocessed clauses: 0
% 0.20/0.41  # ...number of literals in the above   : 0
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 23
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 12681
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 770
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 49
% 0.20/0.41  # Unit Clause-clause subsumption calls : 19
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 1
% 0.20/0.41  # BW rewrite match successes           : 0
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 11996
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.055 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.060 s
% 0.20/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
