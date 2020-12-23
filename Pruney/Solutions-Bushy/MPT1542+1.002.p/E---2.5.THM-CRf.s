%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1542+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:22 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :   91 (23928 expanded)
%              Number of clauses        :   78 (9207 expanded)
%              Number of leaves         :    5 (5787 expanded)
%              Depth                    :   19
%              Number of atoms          :  556 (247573 expanded)
%              Number of equality atoms :   16 (3948 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_lattice3)).

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

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(c_0_4,plain,(
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

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_4])).

fof(c_0_7,plain,(
    ! [X6,X7,X8,X10,X13] :
      ( ( m1_subset_1(esk1_3(X6,X7,X8),u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,X7,esk1_3(X6,X7,X8))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,X8,esk1_3(X6,X7,X8))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_orders_2(X6,X7,X10)
        | ~ r1_orders_2(X6,X8,X10)
        | r1_orders_2(X6,esk1_3(X6,X7,X8),X10)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_1(X6),u1_struct_0(X6))
        | v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk3_1(X6),u1_struct_0(X6))
        | v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_2(X6,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_orders_2(X6,esk2_1(X6),X13)
        | ~ r1_orders_2(X6,esk3_1(X6),X13)
        | v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk2_1(X6),esk4_2(X6,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_orders_2(X6,esk2_1(X6),X13)
        | ~ r1_orders_2(X6,esk3_1(X6),X13)
        | v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk3_1(X6),esk4_2(X6,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_orders_2(X6,esk2_1(X6),X13)
        | ~ r1_orders_2(X6,esk3_1(X6),X13)
        | v1_lattice3(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r1_orders_2(X6,X13,esk4_2(X6,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_orders_2(X6,esk2_1(X6),X13)
        | ~ r1_orders_2(X6,esk3_1(X6),X13)
        | v1_lattice3(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_lattice3])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X24,X25] :
      ( v5_orders_2(esk5_0)
      & l1_orders_2(esk5_0)
      & ( m1_subset_1(esk6_0,u1_struct_0(esk5_0))
        | ~ v1_lattice3(esk5_0) )
      & ( m1_subset_1(esk7_0,u1_struct_0(esk5_0))
        | ~ v1_lattice3(esk5_0) )
      & ( ~ r1_yellow_0(esk5_0,k2_tarski(esk6_0,esk7_0))
        | ~ v1_lattice3(esk5_0) )
      & ( v1_lattice3(esk5_0)
        | ~ m1_subset_1(X24,u1_struct_0(esk5_0))
        | ~ m1_subset_1(X25,u1_struct_0(esk5_0))
        | r1_yellow_0(esk5_0,k2_tarski(X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_9,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => epred1_3(X3,X1,X2) ) ) ) ),
    inference(apply_def,[status(thm)],[t18_yellow_0,c_0_4])).

fof(c_0_10,plain,(
    ! [X26,X27,X28,X29,X30] :
      ( ( r1_orders_2(X27,X26,X29)
        | X29 != k10_lattice3(X27,X26,X28)
        | ~ r1_yellow_0(X27,k2_tarski(X26,X28))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( r1_orders_2(X27,X28,X29)
        | X29 != k10_lattice3(X27,X26,X28)
        | ~ r1_yellow_0(X27,k2_tarski(X26,X28))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r1_orders_2(X27,X26,X30)
        | ~ r1_orders_2(X27,X28,X30)
        | r1_orders_2(X27,X29,X30)
        | X29 != k10_lattice3(X27,X26,X28)
        | ~ r1_yellow_0(X27,k2_tarski(X26,X28))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( X29 = k10_lattice3(X27,X26,X28)
        | m1_subset_1(esk8_4(X26,X27,X28,X29),u1_struct_0(X27))
        | ~ r1_orders_2(X27,X26,X29)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( r1_yellow_0(X27,k2_tarski(X26,X28))
        | m1_subset_1(esk8_4(X26,X27,X28,X29),u1_struct_0(X27))
        | ~ r1_orders_2(X27,X26,X29)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( X29 = k10_lattice3(X27,X26,X28)
        | r1_orders_2(X27,X26,esk8_4(X26,X27,X28,X29))
        | ~ r1_orders_2(X27,X26,X29)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( r1_yellow_0(X27,k2_tarski(X26,X28))
        | r1_orders_2(X27,X26,esk8_4(X26,X27,X28,X29))
        | ~ r1_orders_2(X27,X26,X29)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( X29 = k10_lattice3(X27,X26,X28)
        | r1_orders_2(X27,X28,esk8_4(X26,X27,X28,X29))
        | ~ r1_orders_2(X27,X26,X29)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( r1_yellow_0(X27,k2_tarski(X26,X28))
        | r1_orders_2(X27,X28,esk8_4(X26,X27,X28,X29))
        | ~ r1_orders_2(X27,X26,X29)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( X29 = k10_lattice3(X27,X26,X28)
        | ~ r1_orders_2(X27,X29,esk8_4(X26,X27,X28,X29))
        | ~ r1_orders_2(X27,X26,X29)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) )
      & ( r1_yellow_0(X27,k2_tarski(X26,X28))
        | ~ r1_orders_2(X27,X29,esk8_4(X26,X27,X28,X29))
        | ~ r1_orders_2(X27,X26,X29)
        | ~ r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ epred1_3(X28,X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X18,X19,X20] :
      ( ~ v5_orders_2(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | epred1_3(X20,X18,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X4,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X2,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X15,X16,X17] :
      ( ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | m1_subset_1(k10_lattice3(X15,X16,X17),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

cnf(c_0_16,negated_conjecture,
    ( v1_lattice3(esk5_0)
    | r1_yellow_0(esk5_0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_1(esk5_0),u1_struct_0(esk5_0))
    | v1_lattice3(esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( epred1_3(X3,X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X4,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ epred1_3(X2,X1,X3)
    | ~ r1_yellow_0(X1,k2_tarski(X3,X2))
    | ~ m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(X1,esk2_1(esk5_0)))
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_1(esk5_0),u1_struct_0(esk5_0))
    | v1_lattice3(esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( epred1_3(esk2_1(esk5_0),esk5_0,X1)
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_20]),c_0_12])])).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_orders_2(X2,X5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k10_lattice3(X2,X3,X4)
    | ~ r1_yellow_0(X2,k2_tarski(X3,X4))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ epred1_3(X2,X1,X3)
    | ~ r1_yellow_0(X1,k2_tarski(X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(esk3_1(esk5_0),esk2_1(esk5_0)))
    | v1_lattice3(esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( epred1_3(esk2_1(esk5_0),esk5_0,esk3_1(esk5_0))
    | v1_lattice3(esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_32,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_33,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,esk2_1(X1),esk4_2(X1,X2))
    | v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk2_1(X1),X2)
    | ~ r1_orders_2(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk5_0,esk2_1(esk5_0),k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0)))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_12])]),c_0_25]),c_0_17]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk5_0,esk3_1(esk5_0),k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0)))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_12])]),c_0_25]),c_0_17]),c_0_31])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk2_1(X1),X2)
    | ~ r1_orders_2(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,esk3_1(X1),esk4_2(X1,X2))
    | v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk2_1(X1),X2)
    | ~ r1_orders_2(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk8_4(X2,X1,X3,X4),u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk5_0,esk2_1(esk5_0),esk4_2(esk5_0,k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0))))
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_12])]),c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0))),u1_struct_0(esk5_0))
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_35]),c_0_12])]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk5_0,esk3_1(esk5_0),esk4_2(esk5_0,k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0))))
    | v1_lattice3(esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_12])]),c_0_36])).

cnf(c_0_45,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk8_4(X2,X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk8_4(X2,X1,X3,esk1_3(X1,X4,X5)),u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X3,esk1_3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_orders_2(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk5_0,k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0)),X1)
    | v1_lattice3(esk5_0)
    | ~ r1_orders_2(esk5_0,esk2_1(esk5_0),X1)
    | ~ r1_orders_2(esk5_0,esk3_1(esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_12])]),c_0_25]),c_0_17]),c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk5_0,esk2_1(esk5_0),esk4_2(esk5_0,k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0))))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_23]),c_0_12])]),c_0_25]),c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0))),u1_struct_0(esk5_0))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_23]),c_0_12])]),c_0_25]),c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk5_0,esk3_1(esk5_0),esk4_2(esk5_0,k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0))))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_23]),c_0_12])]),c_0_25]),c_0_17])).

cnf(c_0_52,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk8_4(X2,X1,X3,esk1_3(X1,X4,X5)))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X3,esk1_3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_53,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk8_4(X2,X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk8_4(X2,X1,X3,esk1_3(X1,X3,X4)),u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_56,plain,
    ( v1_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk4_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk2_1(X1),X2)
    | ~ r1_orders_2(X1,esk3_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk5_0,k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0)),esk4_2(esk5_0,k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0))))
    | v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_58,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk8_4(X2,X1,X3,esk1_3(X1,X3,X4)))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_59,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk8_4(X2,X1,X3,esk1_3(X1,X4,X5)))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X3,esk1_3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_60,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk8_4(X2,X1,X3,esk1_3(X1,X3,X2)),u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_62,negated_conjecture,
    ( v1_lattice3(esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk5_0,esk3_1(esk5_0),esk2_1(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_12])]),c_0_36]),c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_64,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk8_4(X2,X1,X3,esk1_3(X1,X3,X2)))
    | ~ epred1_3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_55])).

cnf(c_0_65,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk8_4(X2,X1,X3,esk1_3(X1,X3,X4)))
    | ~ epred1_3(X3,X1,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_47])).

cnf(c_0_66,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(esk6_0,X1))
    | m1_subset_1(esk8_4(esk6_0,esk5_0,X1,esk1_3(esk5_0,X1,esk6_0)),u1_struct_0(esk5_0))
    | ~ epred1_3(X1,esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_12])])).

cnf(c_0_67,negated_conjecture,
    ( v1_lattice3(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_23]),c_0_12])]),c_0_25]),c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( epred1_3(esk7_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_63]),c_0_20]),c_0_12])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_yellow_0(esk5_0,k2_tarski(esk6_0,esk7_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_70,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(esk6_0,X1))
    | r1_orders_2(esk5_0,X1,esk8_4(esk6_0,esk5_0,X1,esk1_3(esk5_0,X1,esk6_0)))
    | ~ epred1_3(X1,esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_61]),c_0_12])])).

cnf(c_0_71,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk8_4(X2,X1,X3,esk1_3(X1,X3,X2)))
    | ~ epred1_3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_55])).

cnf(c_0_72,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X4,esk8_4(X2,X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_73,plain,
    ( r1_orders_2(X2,esk1_3(X2,X3,X4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_74,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(esk6_0,X1))
    | m1_subset_1(esk8_4(esk6_0,esk5_0,X1,esk1_3(esk5_0,X1,esk6_0)),u1_struct_0(esk5_0))
    | ~ epred1_3(X1,esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_75,negated_conjecture,
    ( epred1_3(esk7_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_67])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_67])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_67])])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_yellow_0(esk5_0,k2_tarski(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_67])])).

cnf(c_0_79,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(esk6_0,X1))
    | r1_orders_2(esk5_0,X1,esk8_4(esk6_0,esk5_0,X1,esk1_3(esk5_0,X1,esk6_0)))
    | ~ epred1_3(X1,esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_67])])).

cnf(c_0_80,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(esk6_0,X1))
    | r1_orders_2(esk5_0,esk6_0,esk8_4(esk6_0,esk5_0,X1,esk1_3(esk5_0,X1,esk6_0)))
    | ~ epred1_3(X1,esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v1_lattice3(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_61]),c_0_12])])).

cnf(c_0_81,plain,
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
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_40])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk8_4(esk6_0,esk5_0,esk7_0,esk1_3(esk5_0,esk7_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77])]),c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk8_4(esk6_0,esk5_0,esk7_0,esk1_3(esk5_0,esk7_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_75]),c_0_76]),c_0_77])]),c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( r1_yellow_0(esk5_0,k2_tarski(esk6_0,X1))
    | r1_orders_2(esk5_0,esk6_0,esk8_4(esk6_0,esk5_0,X1,esk1_3(esk5_0,X1,esk6_0)))
    | ~ epred1_3(X1,esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_67])])).

cnf(c_0_85,plain,
    ( ~ epred1_3(esk7_0,esk5_0,esk6_0)
    | ~ r1_orders_2(esk5_0,esk6_0,esk8_4(esk6_0,esk5_0,esk7_0,esk1_3(esk5_0,esk7_0,esk6_0)))
    | ~ r1_orders_2(esk5_0,esk7_0,esk1_3(esk5_0,esk7_0,esk6_0))
    | ~ r1_orders_2(esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_77]),c_0_76]),c_0_67]),c_0_12])]),c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( r1_orders_2(esk5_0,esk6_0,esk8_4(esk6_0,esk5_0,esk7_0,esk1_3(esk5_0,esk7_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_75]),c_0_76]),c_0_77])]),c_0_78])).

cnf(c_0_87,plain,
    ( ~ epred1_3(esk7_0,esk5_0,esk6_0)
    | ~ r1_orders_2(esk5_0,esk7_0,esk1_3(esk5_0,esk7_0,esk6_0))
    | ~ r1_orders_2(esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_88,plain,
    ( ~ epred1_3(esk7_0,esk5_0,esk6_0)
    | ~ r1_orders_2(esk5_0,esk6_0,esk1_3(esk5_0,esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_47]),c_0_77]),c_0_76]),c_0_67]),c_0_12])])).

cnf(c_0_89,plain,
    ( ~ epred1_3(esk7_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_55]),c_0_76]),c_0_77]),c_0_67]),c_0_12])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_75]),c_0_77])]),
    [proof]).

%------------------------------------------------------------------------------
