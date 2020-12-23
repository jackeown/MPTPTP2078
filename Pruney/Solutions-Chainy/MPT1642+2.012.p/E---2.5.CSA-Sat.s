%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:14 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   74 (1109 expanded)
%              Number of clauses        :   61 ( 372 expanded)
%              Number of leaves         :    5 ( 267 expanded)
%              Depth                    :    7
%              Number of atoms          :  298 (7084 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(c_0_4,plain,(
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

fof(c_0_5,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => epred1_4(X2,X3,X4,X1) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t8_yellow_0,c_0_4])).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | epred1_4(X14,X15,X16,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & r1_orders_2(esk2_0,esk3_0,esk4_0)
    & ~ r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ r1_lattice3(X9,X12,X11)
        | r1_lattice3(X9,X12,X10)
        | ~ r1_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v4_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ r2_lattice3(X9,X12,X10)
        | r2_lattice3(X9,X12,X11)
        | ~ r1_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v4_orders_2(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).

fof(c_0_10,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( epred1_4(X2,X3,X4,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_15,plain,
    ( r2_lattice3(X1,X2,X4)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_17,plain,
    ( r1_lattice3(X1,X2,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

fof(c_0_18,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r1_orders_2(X20,X23,X22)
        | ~ r1_lattice3(X20,k2_tarski(X22,X21),X23)
        | ~ epred1_4(X23,X22,X21,X20) )
      & ( r1_orders_2(X20,X23,X21)
        | ~ r1_lattice3(X20,k2_tarski(X22,X21),X23)
        | ~ epred1_4(X23,X22,X21,X20) )
      & ( ~ r1_orders_2(X20,X23,X22)
        | ~ r1_orders_2(X20,X23,X21)
        | r1_lattice3(X20,k2_tarski(X22,X21),X23)
        | ~ epred1_4(X23,X22,X21,X20) )
      & ( r1_orders_2(X20,X22,X23)
        | ~ r2_lattice3(X20,k2_tarski(X22,X21),X23)
        | ~ epred1_4(X23,X22,X21,X20) )
      & ( r1_orders_2(X20,X21,X23)
        | ~ r2_lattice3(X20,k2_tarski(X22,X21),X23)
        | ~ epred1_4(X23,X22,X21,X20) )
      & ( ~ r1_orders_2(X20,X22,X23)
        | ~ r1_orders_2(X20,X21,X23)
        | r2_lattice3(X20,k2_tarski(X22,X21),X23)
        | ~ epred1_4(X23,X22,X21,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_19,negated_conjecture,
    ( epred1_4(X1,X2,esk4_0,esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( epred1_4(X1,X2,esk3_0,esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_14]),c_0_13])]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_lattice3(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,X2,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_12]),c_0_13]),c_0_16])]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk3_0)
    | ~ r1_lattice3(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,esk3_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_13]),c_0_16])]),
    [final]).

cnf(c_0_24,plain,
    ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ epred1_4(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( epred1_4(X1,esk3_0,esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_14]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( epred1_4(X1,esk4_0,esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_12]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( epred1_4(X1,esk3_0,esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_14]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( epred1_4(X1,esk4_0,esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,esk4_0)
    | ~ r1_lattice3(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,esk4_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_12]),c_0_13]),c_0_16])]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_lattice3(esk2_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14])]),
    [final]).

cnf(c_0_31,plain,
    ( r2_lattice3(X1,k2_tarski(X2,X4),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ epred1_4(X3,X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_32,plain,
    ( r1_lattice3(esk2_0,k2_tarski(X1,X2),esk3_0)
    | ~ epred1_4(X3,X1,X2,esk2_0)
    | ~ r1_orders_2(esk2_0,esk3_0,X3)
    | ~ r1_orders_2(esk2_0,X3,X2)
    | ~ r1_orders_2(esk2_0,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( epred1_4(esk4_0,esk3_0,esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_12]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( epred1_4(esk4_0,esk4_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_12]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( epred1_4(esk3_0,esk3_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_14]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( epred1_4(esk3_0,esk3_0,esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( epred1_4(esk3_0,esk4_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_14]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( epred1_4(esk3_0,esk4_0,esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_14]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( epred1_4(esk4_0,esk3_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_12]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( epred1_4(esk4_0,esk4_0,esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_12]),
    [final]).

cnf(c_0_41,plain,
    ( r1_lattice3(esk2_0,k2_tarski(X1,X2),esk4_0)
    | ~ epred1_4(X3,X1,X2,esk2_0)
    | ~ r1_orders_2(esk2_0,esk4_0,X3)
    | ~ r1_orders_2(esk2_0,X3,X2)
    | ~ r1_orders_2(esk2_0,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24]),
    [final]).

cnf(c_0_42,plain,
    ( r2_lattice3(esk2_0,k2_tarski(X1,X2),esk4_0)
    | ~ epred1_4(esk3_0,X1,X2,esk2_0)
    | ~ r1_orders_2(esk2_0,X2,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31]),
    [final]).

fof(c_0_43,plain,(
    ! [X5,X6,X7] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),X5)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( ~ r2_hidden(esk1_3(X5,X6,X7),X7)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22]),c_0_12])]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_34]),c_0_22]),c_0_12])]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_35]),c_0_14])]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_36]),c_0_22]),c_0_14])]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_22]),c_0_14])]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_22]),c_0_14])]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_39]),c_0_22]),c_0_12])]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_40]),c_0_22]),c_0_12])]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_14])]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_22]),c_0_14])]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_22]),c_0_14])]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_12])]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_33]),c_0_12])]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_34]),c_0_12])]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r2_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_36]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_22]),c_0_14])]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r1_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_12])]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( r2_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_35]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( r2_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk3_0)
    | ~ r2_lattice3(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,X2,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_14]),c_0_13]),c_0_16])]),
    [final]).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_66,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_67,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_lattice3(X1,k2_tarski(X3,X4),X2)
    | ~ epred1_4(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_68,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_lattice3(X1,k2_tarski(X4,X3),X2)
    | ~ epred1_4(X2,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_69,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k2_tarski(X2,X4),X3)
    | ~ epred1_4(X3,X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_70,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k2_tarski(X4,X2),X3)
    | ~ epred1_4(X3,X4,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_71,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S07FI
% 0.14/0.38  # and selection function SelectCQArNXTEqFirst.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(t8_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_yellow_0)).
% 0.14/0.38  fof(t22_waybel_0, conjecture, ![X1]:(((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_waybel_0)).
% 0.14/0.38  fof(t4_yellow_0, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>![X4]:((r1_lattice3(X1,X4,X3)=>r1_lattice3(X1,X4,X2))&(r2_lattice3(X1,X4,X2)=>r2_lattice3(X1,X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_0)).
% 0.14/0.38  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.14/0.38  fof(c_0_4, plain, ![X1, X4, X3, X2]:(epred1_4(X2,X3,X4,X1)<=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2)))), introduced(definition)).
% 0.14/0.38  fof(c_0_5, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>epred1_4(X2,X3,X4,X1))))), inference(apply_def,[status(thm)],[t8_yellow_0, c_0_4])).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2))))))), inference(assume_negation,[status(cth)],[t22_waybel_0])).
% 0.14/0.38  fof(c_0_7, plain, ![X13, X14, X15, X16]:(~l1_orders_2(X13)|(~m1_subset_1(X14,u1_struct_0(X13))|(~m1_subset_1(X15,u1_struct_0(X13))|(~m1_subset_1(X16,u1_struct_0(X13))|epred1_4(X14,X15,X16,X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, (((~v2_struct_0(esk2_0)&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(r1_orders_2(esk2_0,esk3_0,esk4_0)&~r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X9, X10, X11, X12]:((~r1_lattice3(X9,X12,X11)|r1_lattice3(X9,X12,X10)|~r1_orders_2(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(~v4_orders_2(X9)|~l1_orders_2(X9)))&(~r2_lattice3(X9,X12,X10)|r2_lattice3(X9,X12,X11)|~r1_orders_2(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(~v4_orders_2(X9)|~l1_orders_2(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X1, X4, X3, X2]:(epred1_4(X2,X3,X4,X1)=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2)))), inference(split_equiv,[status(thm)],[c_0_4])).
% 0.14/0.38  cnf(c_0_11, plain, (epred1_4(X2,X3,X4,X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_15, plain, (r2_lattice3(X1,X2,X4)|~r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_17, plain, (r1_lattice3(X1,X2,X4)|~r1_lattice3(X1,X2,X3)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  fof(c_0_18, plain, ![X20, X21, X22, X23]:(((((r1_orders_2(X20,X23,X22)|~r1_lattice3(X20,k2_tarski(X22,X21),X23)|~epred1_4(X23,X22,X21,X20))&(r1_orders_2(X20,X23,X21)|~r1_lattice3(X20,k2_tarski(X22,X21),X23)|~epred1_4(X23,X22,X21,X20)))&(~r1_orders_2(X20,X23,X22)|~r1_orders_2(X20,X23,X21)|r1_lattice3(X20,k2_tarski(X22,X21),X23)|~epred1_4(X23,X22,X21,X20)))&((r1_orders_2(X20,X22,X23)|~r2_lattice3(X20,k2_tarski(X22,X21),X23)|~epred1_4(X23,X22,X21,X20))&(r1_orders_2(X20,X21,X23)|~r2_lattice3(X20,k2_tarski(X22,X21),X23)|~epred1_4(X23,X22,X21,X20))))&(~r1_orders_2(X20,X22,X23)|~r1_orders_2(X20,X21,X23)|r2_lattice3(X20,k2_tarski(X22,X21),X23)|~epred1_4(X23,X22,X21,X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (epred1_4(X1,X2,esk4_0,esk2_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (epred1_4(X1,X2,esk3_0,esk2_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_14]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (r2_lattice3(esk2_0,X1,esk4_0)|~r2_lattice3(esk2_0,X1,X2)|~r1_orders_2(esk2_0,X2,esk4_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_12]), c_0_13]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r1_lattice3(esk2_0,X1,esk3_0)|~r1_lattice3(esk2_0,X1,X2)|~r1_orders_2(esk2_0,esk3_0,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_14]), c_0_13]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_24, plain, (r1_lattice3(X1,k2_tarski(X3,X4),X2)|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X4)|~epred1_4(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (epred1_4(X1,esk3_0,esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_19, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (epred1_4(X1,esk4_0,esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_20, c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (epred1_4(X1,esk3_0,esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_20, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (epred1_4(X1,esk4_0,esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_19, c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r1_lattice3(esk2_0,X1,esk4_0)|~r1_lattice3(esk2_0,X1,X2)|~r1_orders_2(esk2_0,esk4_0,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_12]), c_0_13]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (r2_lattice3(esk2_0,X1,esk4_0)|~r2_lattice3(esk2_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_14])]), ['final']).
% 0.14/0.38  cnf(c_0_31, plain, (r2_lattice3(X1,k2_tarski(X2,X4),X3)|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X4,X3)|~epred1_4(X3,X2,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_32, plain, (r1_lattice3(esk2_0,k2_tarski(X1,X2),esk3_0)|~epred1_4(X3,X1,X2,esk2_0)|~r1_orders_2(esk2_0,esk3_0,X3)|~r1_orders_2(esk2_0,X3,X2)|~r1_orders_2(esk2_0,X3,X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_24]), ['final']).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (epred1_4(esk4_0,esk3_0,esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (epred1_4(esk4_0,esk4_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (epred1_4(esk3_0,esk3_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (epred1_4(esk3_0,esk3_0,esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (epred1_4(esk3_0,esk4_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (epred1_4(esk3_0,esk4_0,esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (epred1_4(esk4_0,esk3_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (epred1_4(esk4_0,esk4_0,esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_41, plain, (r1_lattice3(esk2_0,k2_tarski(X1,X2),esk4_0)|~epred1_4(X3,X1,X2,esk2_0)|~r1_orders_2(esk2_0,esk4_0,X3)|~r1_orders_2(esk2_0,X3,X2)|~r1_orders_2(esk2_0,X3,X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_24]), ['final']).
% 0.14/0.38  cnf(c_0_42, plain, (r2_lattice3(esk2_0,k2_tarski(X1,X2),esk4_0)|~epred1_4(esk3_0,X1,X2,esk2_0)|~r1_orders_2(esk2_0,X2,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31]), ['final']).
% 0.14/0.38  fof(c_0_43, plain, ![X5, X6, X7]:((m1_subset_1(esk1_3(X5,X6,X7),X5)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&((r2_hidden(esk1_3(X5,X6,X7),X6)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&(~r2_hidden(esk1_3(X5,X6,X7),X7)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk3_0)|~r1_orders_2(esk2_0,esk4_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22]), c_0_12])]), ['final']).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk3_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_34]), c_0_22]), c_0_12])]), ['final']).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk3_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_35]), c_0_14])]), ['final']).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk3_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_36]), c_0_22]), c_0_14])]), ['final']).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk3_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_22]), c_0_14])]), ['final']).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk3_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_38]), c_0_22]), c_0_14])]), ['final']).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk3_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_39]), c_0_22]), c_0_12])]), ['final']).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk3_0)|~r1_orders_2(esk2_0,esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_40]), c_0_22]), c_0_12])]), ['final']).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_14])]), ['final']).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_36]), c_0_22]), c_0_14])]), ['final']).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_22]), c_0_14])]), ['final']).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_12])]), ['final']).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_33]), c_0_12])]), ['final']).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_34]), c_0_12])]), ['final']).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (r2_lattice3(esk2_0,k2_tarski(esk3_0,esk4_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_36]), ['final']).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (r2_lattice3(esk2_0,k2_tarski(esk4_0,esk3_0),esk4_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_37]), ['final']).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_38]), c_0_22]), c_0_14])]), ['final']).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (r1_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_12])]), ['final']).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (r2_lattice3(esk2_0,k2_tarski(esk3_0,esk3_0),esk4_0)|~r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_35]), ['final']).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (r2_lattice3(esk2_0,k2_tarski(esk4_0,esk4_0),esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_38]), ['final']).
% 0.14/0.38  cnf(c_0_64, negated_conjecture, (r2_lattice3(esk2_0,X1,esk3_0)|~r2_lattice3(esk2_0,X1,X2)|~r1_orders_2(esk2_0,X2,esk3_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_14]), c_0_13]), c_0_16])]), ['final']).
% 0.14/0.38  cnf(c_0_65, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.14/0.38  cnf(c_0_66, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.14/0.38  cnf(c_0_67, plain, (r1_orders_2(X1,X2,X3)|~r1_lattice3(X1,k2_tarski(X3,X4),X2)|~epred1_4(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_68, plain, (r1_orders_2(X1,X2,X3)|~r1_lattice3(X1,k2_tarski(X4,X3),X2)|~epred1_4(X2,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_69, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k2_tarski(X2,X4),X3)|~epred1_4(X3,X2,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_70, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k2_tarski(X4,X2),X3)|~epred1_4(X3,X4,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_71, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, (~r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_73, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 74
% 0.14/0.38  # Proof object clause steps            : 61
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 49
% 0.14/0.38  # Proof object clause conjectures      : 46
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 19
% 0.14/0.38  # Proof object initial formulas used   : 4
% 0.14/0.38  # Proof object generating inferences   : 42
% 0.14/0.38  # Proof object simplifying inferences  : 60
% 0.14/0.38  # Parsed axioms                        : 4
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 19
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 19
% 0.14/0.38  # Processed clauses                    : 80
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 80
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 46
% 0.14/0.38  # ...of the previous two non-trivial   : 42
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 46
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 61
% 0.14/0.38  #    Positive orientable unit clauses  : 13
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 46
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 19
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 521
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 370
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 34
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 4
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2883
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
