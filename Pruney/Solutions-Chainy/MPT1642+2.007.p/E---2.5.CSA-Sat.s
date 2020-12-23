%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:14 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 495 expanded)
%              Number of clauses        :   49 ( 163 expanded)
%              Number of leaves         :    6 ( 123 expanded)
%              Depth                    :    9
%              Number of atoms          :  302 (3237 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
               => r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_0)).

fof(t4_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
               => ! [X4] :
                    ( ( r1_lattice3(X1,X4,X3)
                     => r1_lattice3(X1,X4,X2) )
                    & ( r2_lattice3(X1,X4,X2)
                     => r2_lattice3(X1,X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(t8_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
                     => ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X2,X4) ) )
                    & ( ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X2,X4) )
                     => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
                    & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
                     => ( r1_orders_2(X1,X3,X2)
                        & r1_orders_2(X1,X4,X2) ) )
                    & ( ( r1_orders_2(X1,X3,X2)
                        & r1_orders_2(X1,X4,X2) )
                     => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_orders_2(X1,X2,X3)
                 => r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_waybel_0])).

fof(c_0_6,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r1_lattice3(X14,X17,X16)
        | r1_lattice3(X14,X17,X15)
        | ~ r1_orders_2(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v4_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( ~ r2_lattice3(X14,X17,X15)
        | r2_lattice3(X14,X17,X16)
        | ~ r1_orders_2(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v4_orders_2(X14)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & r1_orders_2(esk2_0,esk3_0,esk4_0)
    & ~ r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X1,X4,X3,X2] :
      ( epred1_4(X2,X3,X4,X1)
    <=> ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) ) )
        & ( ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) )
         => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
        & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) ) )
        & ( ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) )
         => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ),
    introduced(definition)).

cnf(c_0_9,plain,
    ( r1_lattice3(X1,X2,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

fof(c_0_13,plain,(
    ! [X1,X4,X3,X2] :
      ( epred1_4(X2,X3,X4,X1)
     => ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) ) )
        & ( ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) )
         => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
        & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) ) )
        & ( ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) )
         => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_lattice3(X1,X2,X4)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk3_0)
    | ~ r1_lattice3(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,esk3_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

fof(c_0_18,plain,(
    ! [X25,X26,X27,X28] :
      ( ( r1_orders_2(X25,X28,X27)
        | ~ r1_lattice3(X25,k2_tarski(X27,X26),X28)
        | ~ epred1_4(X28,X27,X26,X25) )
      & ( r1_orders_2(X25,X28,X26)
        | ~ r1_lattice3(X25,k2_tarski(X27,X26),X28)
        | ~ epred1_4(X28,X27,X26,X25) )
      & ( ~ r1_orders_2(X25,X28,X27)
        | ~ r1_orders_2(X25,X28,X26)
        | r1_lattice3(X25,k2_tarski(X27,X26),X28)
        | ~ epred1_4(X28,X27,X26,X25) )
      & ( r1_orders_2(X25,X27,X28)
        | ~ r2_lattice3(X25,k2_tarski(X27,X26),X28)
        | ~ epred1_4(X28,X27,X26,X25) )
      & ( r1_orders_2(X25,X26,X28)
        | ~ r2_lattice3(X25,k2_tarski(X27,X26),X28)
        | ~ epred1_4(X28,X27,X26,X25) )
      & ( ~ r1_orders_2(X25,X27,X28)
        | ~ r1_orders_2(X25,X26,X28)
        | r2_lattice3(X25,k2_tarski(X27,X26),X28)
        | ~ epred1_4(X28,X27,X26,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_19,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => epred1_4(X2,X3,X4,X1) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t8_yellow_0,c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_lattice3(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,X2,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_11]),c_0_12])]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk3_0)
    | ~ r1_lattice3(esk2_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_15])]),
    [final]).

cnf(c_0_22,plain,
    ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ epred1_4(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

fof(c_0_23,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | epred1_4(X19,X20,X21,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k2_tarski(X2,X4),X3)
    | ~ epred1_4(X3,X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_lattice3(esk2_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_10])]),
    [final]).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k2_tarski(X4,X2),X3)
    | ~ epred1_4(X3,X4,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_lattice3(X1,k2_tarski(X3,X4),X2)
    | ~ epred1_4(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_28,plain,
    ( r1_lattice3(esk2_0,k2_tarski(X1,X2),esk3_0)
    | ~ epred1_4(esk4_0,X1,X2,esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X2)
    | ~ r1_orders_2(esk2_0,esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22]),
    [final]).

cnf(c_0_29,plain,
    ( epred1_4(X2,X3,X4,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_lattice3(X1,k2_tarski(X4,X3),X2)
    | ~ epred1_4(X2,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_31,plain,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ epred1_4(esk4_0,X1,X2,esk2_0)
    | ~ r2_lattice3(esk2_0,k2_tarski(X1,X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,k2_tarski(X2,X4),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ epred1_4(X3,X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_33,plain,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ epred1_4(esk4_0,X2,X1,esk2_0)
    | ~ r2_lattice3(esk2_0,k2_tarski(X2,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25]),
    [final]).

cnf(c_0_34,plain,
    ( r1_orders_2(esk2_0,esk3_0,X1)
    | ~ epred1_4(esk3_0,X1,X2,esk2_0)
    | ~ epred1_4(esk4_0,X1,X2,esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X2)
    | ~ r1_orders_2(esk2_0,esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( epred1_4(X1,X2,esk3_0,esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_36,plain,
    ( r1_orders_2(esk2_0,esk3_0,X1)
    | ~ epred1_4(esk3_0,X2,X1,esk2_0)
    | ~ epred1_4(esk4_0,X2,X1,esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ r1_orders_2(esk2_0,esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( epred1_4(X1,X2,esk4_0,esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_15]),c_0_11])]),
    [final]).

cnf(c_0_38,plain,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ epred1_4(esk4_0,X1,X2,esk2_0)
    | ~ epred1_4(esk3_0,X1,X2,esk2_0)
    | ~ r1_orders_2(esk2_0,X2,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32]),
    [final]).

cnf(c_0_39,plain,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ epred1_4(esk4_0,X2,X1,esk2_0)
    | ~ epred1_4(esk3_0,X2,X1,esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ r1_orders_2(esk2_0,X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32]),
    [final]).

fof(c_0_40,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,X1)
    | ~ epred1_4(esk3_0,X1,esk3_0,esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_15])])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0)
    | ~ epred1_4(esk3_0,X1,esk3_0,esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,X1)
    | ~ epred1_4(esk3_0,X1,esk4_0,esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_37]),c_0_15])])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ epred1_4(esk3_0,X1,esk3_0,esk2_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_15])])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ epred1_4(esk3_0,X1,esk4_0,esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_15])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ epred1_4(esk3_0,X1,esk4_0,esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_15])])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

fof(c_0_49,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | m1_subset_1(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,X1)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_10])]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_10])]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,X1)
    | ~ r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_10])]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_35]),c_0_10])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_37]),c_0_10])]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_37]),c_0_10])]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk3_0)
    | ~ r2_lattice3(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,X2,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11]),c_0_12])]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk4_0)
    | ~ r1_lattice3(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,esk4_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_15]),c_0_11]),c_0_12])]),
    [final]).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48]),
    [final]).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:36:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S5PRR_S04BN
% 0.13/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # No proof found!
% 0.13/0.37  # SZS status CounterSatisfiable
% 0.13/0.37  # SZS output start Saturation
% 0.13/0.37  fof(t22_waybel_0, conjecture, ![X1]:(((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_waybel_0)).
% 0.13/0.37  fof(t4_yellow_0, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>![X4]:((r1_lattice3(X1,X4,X3)=>r1_lattice3(X1,X4,X2))&(r2_lattice3(X1,X4,X2)=>r2_lattice3(X1,X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_0)).
% 0.13/0.37  fof(t8_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_yellow_0)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2))))))), inference(assume_negation,[status(cth)],[t22_waybel_0])).
% 0.13/0.37  fof(c_0_6, plain, ![X14, X15, X16, X17]:((~r1_lattice3(X14,X17,X16)|r1_lattice3(X14,X17,X15)|~r1_orders_2(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~m1_subset_1(X15,u1_struct_0(X14))|(~v4_orders_2(X14)|~l1_orders_2(X14)))&(~r2_lattice3(X14,X17,X15)|r2_lattice3(X14,X17,X16)|~r1_orders_2(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~m1_subset_1(X15,u1_struct_0(X14))|(~v4_orders_2(X14)|~l1_orders_2(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, (((~v2_struct_0(esk2_0)&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(r1_orders_2(esk2_0,esk3_0,esk4_0)&~r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.13/0.37  fof(c_0_8, plain, ![X1, X4, X3, X2]:(epred1_4(X2,X3,X4,X1)<=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2)))), introduced(definition)).
% 0.13/0.37  cnf(c_0_9, plain, (r1_lattice3(X1,X2,X4)|~r1_lattice3(X1,X2,X3)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  fof(c_0_13, plain, ![X1, X4, X3, X2]:(epred1_4(X2,X3,X4,X1)=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2)))), inference(split_equiv,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, plain, (r2_lattice3(X1,X2,X4)|~r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (r1_lattice3(esk2_0,X1,esk3_0)|~r1_lattice3(esk2_0,X1,X2)|~r1_orders_2(esk2_0,esk3_0,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])]), ['final']).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  fof(c_0_18, plain, ![X25, X26, X27, X28]:(((((r1_orders_2(X25,X28,X27)|~r1_lattice3(X25,k2_tarski(X27,X26),X28)|~epred1_4(X28,X27,X26,X25))&(r1_orders_2(X25,X28,X26)|~r1_lattice3(X25,k2_tarski(X27,X26),X28)|~epred1_4(X28,X27,X26,X25)))&(~r1_orders_2(X25,X28,X27)|~r1_orders_2(X25,X28,X26)|r1_lattice3(X25,k2_tarski(X27,X26),X28)|~epred1_4(X28,X27,X26,X25)))&((r1_orders_2(X25,X27,X28)|~r2_lattice3(X25,k2_tarski(X27,X26),X28)|~epred1_4(X28,X27,X26,X25))&(r1_orders_2(X25,X26,X28)|~r2_lattice3(X25,k2_tarski(X27,X26),X28)|~epred1_4(X28,X27,X26,X25))))&(~r1_orders_2(X25,X27,X28)|~r1_orders_2(X25,X26,X28)|r2_lattice3(X25,k2_tarski(X27,X26),X28)|~epred1_4(X28,X27,X26,X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.37  fof(c_0_19, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>epred1_4(X2,X3,X4,X1))))), inference(apply_def,[status(thm)],[t8_yellow_0, c_0_8])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (r2_lattice3(esk2_0,X1,esk4_0)|~r2_lattice3(esk2_0,X1,X2)|~r1_orders_2(esk2_0,X2,esk4_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_11]), c_0_12])]), ['final']).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (r1_lattice3(esk2_0,X1,esk3_0)|~r1_lattice3(esk2_0,X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_15])]), ['final']).
% 0.13/0.37  cnf(c_0_22, plain, (r1_lattice3(X1,k2_tarski(X3,X4),X2)|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X4)|~epred1_4(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.37  fof(c_0_23, plain, ![X18, X19, X20, X21]:(~l1_orders_2(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|(~m1_subset_1(X20,u1_struct_0(X18))|(~m1_subset_1(X21,u1_struct_0(X18))|epred1_4(X19,X20,X21,X18))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.13/0.37  cnf(c_0_24, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k2_tarski(X2,X4),X3)|~epred1_4(X3,X2,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r2_lattice3(esk2_0,X1,esk4_0)|~r2_lattice3(esk2_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_10])]), ['final']).
% 0.13/0.37  cnf(c_0_26, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k2_tarski(X4,X2),X3)|~epred1_4(X3,X4,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_27, plain, (r1_orders_2(X1,X2,X3)|~r1_lattice3(X1,k2_tarski(X3,X4),X2)|~epred1_4(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_28, plain, (r1_lattice3(esk2_0,k2_tarski(X1,X2),esk3_0)|~epred1_4(esk4_0,X1,X2,esk2_0)|~r1_orders_2(esk2_0,esk4_0,X2)|~r1_orders_2(esk2_0,esk4_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22]), ['final']).
% 0.13/0.37  cnf(c_0_29, plain, (epred1_4(X2,X3,X4,X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.37  cnf(c_0_30, plain, (r1_orders_2(X1,X2,X3)|~r1_lattice3(X1,k2_tarski(X4,X3),X2)|~epred1_4(X2,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_31, plain, (r1_orders_2(esk2_0,X1,esk4_0)|~epred1_4(esk4_0,X1,X2,esk2_0)|~r2_lattice3(esk2_0,k2_tarski(X1,X2),esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.13/0.37  cnf(c_0_32, plain, (r2_lattice3(X1,k2_tarski(X2,X4),X3)|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X4,X3)|~epred1_4(X3,X2,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_33, plain, (r1_orders_2(esk2_0,X1,esk4_0)|~epred1_4(esk4_0,X2,X1,esk2_0)|~r2_lattice3(esk2_0,k2_tarski(X2,X1),esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_25]), ['final']).
% 0.13/0.37  cnf(c_0_34, plain, (r1_orders_2(esk2_0,esk3_0,X1)|~epred1_4(esk3_0,X1,X2,esk2_0)|~epred1_4(esk4_0,X1,X2,esk2_0)|~r1_orders_2(esk2_0,esk4_0,X2)|~r1_orders_2(esk2_0,esk4_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (epred1_4(X1,X2,esk3_0,esk2_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_10]), c_0_11])]), ['final']).
% 0.13/0.37  cnf(c_0_36, plain, (r1_orders_2(esk2_0,esk3_0,X1)|~epred1_4(esk3_0,X2,X1,esk2_0)|~epred1_4(esk4_0,X2,X1,esk2_0)|~r1_orders_2(esk2_0,esk4_0,X1)|~r1_orders_2(esk2_0,esk4_0,X2)), inference(spm,[status(thm)],[c_0_30, c_0_28]), ['final']).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (epred1_4(X1,X2,esk4_0,esk2_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_15]), c_0_11])]), ['final']).
% 0.13/0.37  cnf(c_0_38, plain, (r1_orders_2(esk2_0,X1,esk4_0)|~epred1_4(esk4_0,X1,X2,esk2_0)|~epred1_4(esk3_0,X1,X2,esk2_0)|~r1_orders_2(esk2_0,X2,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32]), ['final']).
% 0.13/0.37  cnf(c_0_39, plain, (r1_orders_2(esk2_0,X1,esk4_0)|~epred1_4(esk4_0,X2,X1,esk2_0)|~epred1_4(esk3_0,X2,X1,esk2_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~r1_orders_2(esk2_0,X2,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_32]), ['final']).
% 0.13/0.37  fof(c_0_40, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,X1)|~epred1_4(esk3_0,X1,esk3_0,esk2_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_15])])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)|~epred1_4(esk3_0,X1,esk3_0,esk2_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_15])])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,X1)|~epred1_4(esk3_0,X1,esk4_0,esk2_0)|~r1_orders_2(esk2_0,esk4_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_37]), c_0_15])])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~epred1_4(esk3_0,X1,esk3_0,esk2_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_15])])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~epred1_4(esk3_0,X1,esk4_0,esk2_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_15])])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk4_0)|~epred1_4(esk3_0,X1,esk4_0,esk2_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_37]), c_0_15])])).
% 0.13/0.37  cnf(c_0_47, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.13/0.37  cnf(c_0_48, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.13/0.37  fof(c_0_49, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|m1_subset_1(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.37  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_40]), ['final']).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,X1)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_10])]), ['final']).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_10])]), ['final']).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,X1)|~r1_orders_2(esk2_0,esk4_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_37]), c_0_10])]), ['final']).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_35]), c_0_10])]), ['final']).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_37]), c_0_10])]), ['final']).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_37]), c_0_10])]), ['final']).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (r2_lattice3(esk2_0,X1,esk3_0)|~r2_lattice3(esk2_0,X1,X2)|~r1_orders_2(esk2_0,X2,esk3_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_10]), c_0_11]), c_0_12])]), ['final']).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, (r1_lattice3(esk2_0,X1,esk4_0)|~r1_lattice3(esk2_0,X1,X2)|~r1_orders_2(esk2_0,esk4_0,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_15]), c_0_11]), c_0_12])]), ['final']).
% 0.13/0.37  cnf(c_0_59, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_48]), ['final']).
% 0.13/0.37  cnf(c_0_60, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.13/0.37  cnf(c_0_61, negated_conjecture, (~r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_50, c_0_48]), ['final']).
% 0.13/0.37  # SZS output end Saturation
% 0.13/0.37  # Proof object total steps             : 64
% 0.13/0.37  # Proof object clause steps            : 49
% 0.13/0.37  # Proof object formula steps           : 15
% 0.13/0.37  # Proof object conjectures             : 30
% 0.13/0.37  # Proof object clause conjectures      : 27
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 20
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 29
% 0.13/0.37  # Proof object simplifying inferences  : 44
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 20
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 20
% 0.13/0.37  # Processed clauses                    : 70
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 69
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 6
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 36
% 0.13/0.37  # ...of the previous two non-trivial   : 30
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 36
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 43
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 35
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 26
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 492
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 131
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.13/0.37  # Unit Clause-clause subsumption calls : 2
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 3
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2923
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.034 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
