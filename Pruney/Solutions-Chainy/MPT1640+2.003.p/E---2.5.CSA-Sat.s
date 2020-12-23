%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:11 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  110 (1149 expanded)
%              Number of clauses        :   99 ( 402 expanded)
%              Number of leaves         :    5 ( 290 expanded)
%              Depth                    :    7
%              Number of atoms          :  683 (10148 expanded)
%              Number of equality atoms :   43 (1362 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

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

fof(t31_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) )
               => ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) )
              & ( ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) )
               => ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

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

fof(c_0_5,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X14,X12)
        | r1_orders_2(X11,X13,X14)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X11))
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,X13,esk1_3(X11,X12,X13))
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_6,negated_conjecture,(
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

cnf(c_0_7,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_8,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v3_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | r3_orders_2(X8,X9,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & k6_waybel_0(esk3_0,esk4_0) = k6_waybel_0(esk3_0,esk5_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_11,plain,
    ( r1_lattice3(X1,X2,X3)
    | r1_orders_2(X1,X4,esk1_3(X1,X2,X3))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X5)
    | ~ r1_lattice3(X1,X5,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8]),
    [final]).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

fof(c_0_13,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( r1_lattice3(X16,X18,X17)
        | X17 != k2_yellow_0(X16,X18)
        | ~ r2_yellow_0(X16,X18)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r1_lattice3(X16,X18,X19)
        | r1_orders_2(X16,X19,X17)
        | X17 != k2_yellow_0(X16,X18)
        | ~ r2_yellow_0(X16,X18)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( X17 = k2_yellow_0(X16,X20)
        | m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))
        | ~ r1_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_yellow_0(X16,X20)
        | m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))
        | ~ r1_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( X17 = k2_yellow_0(X16,X20)
        | r1_lattice3(X16,X20,esk2_3(X16,X17,X20))
        | ~ r1_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_yellow_0(X16,X20)
        | r1_lattice3(X16,X20,esk2_3(X16,X17,X20))
        | ~ r1_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( X17 = k2_yellow_0(X16,X20)
        | ~ r1_orders_2(X16,esk2_3(X16,X17,X20),X17)
        | ~ r1_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_yellow_0(X16,X20)
        | ~ r1_orders_2(X16,esk2_3(X16,X17,X20),X17)
        | ~ r1_lattice3(X16,X20,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

fof(c_0_14,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r3_orders_2(X5,X6,X7)
        | r1_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) )
      & ( ~ r1_orders_2(X5,X6,X7)
        | r3_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_20,plain,
    ( r1_lattice3(X1,X2,X3)
    | r1_orders_2(X1,X4,esk1_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12]),
    [final]).

cnf(c_0_21,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_22,plain,
    ( r2_yellow_0(X1,X2)
    | m1_subset_1(esk2_3(X1,X3,X2),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_23,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( r3_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_27,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_28,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,esk2_3(X2,X1,X3),X1)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_29,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X4,X5)
    | r1_orders_2(X2,esk2_3(X2,X1,X3),esk1_3(X2,X4,X5))
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X4,esk2_3(X2,X1,X3))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_30,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk2_3(X1,X3,X2),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_31,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X3,X4)
    | r1_orders_2(X1,esk2_3(X1,X5,X2),esk1_3(X1,X3,X4))
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,esk2_3(X1,X5,X2))
    | ~ r1_lattice3(X1,X2,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22]),
    [final]).

cnf(c_0_32,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_orders_2(X2,X4,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r3_orders_2(X2,X4,esk2_3(X2,X1,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r3_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk2_3(esk3_0,X1,X2))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_34,plain,
    ( r1_lattice3(X1,X2,X3)
    | r1_orders_2(X1,X4,esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X4,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_8]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r3_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_8]),c_0_17])]),
    [final]).

cnf(c_0_36,plain,
    ( r2_yellow_0(X1,X2)
    | r1_orders_2(X1,X3,esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X4)
    | ~ r3_orders_2(X1,X3,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r3_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk2_3(esk3_0,X2,X1))
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk4_0)
    | ~ r2_hidden(esk4_0,X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_26]),c_0_17])]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk5_0)
    | ~ r2_hidden(esk5_0,X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_16]),c_0_17])]),
    [final]).

cnf(c_0_40,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r3_orders_2(X2,X4,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,esk2_3(X2,X1,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21]),
    [final]).

cnf(c_0_41,plain,
    ( r2_yellow_0(X1,X2)
    | r3_orders_2(X1,X3,esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22]),
    [final]).

cnf(c_0_42,plain,
    ( r1_lattice3(X1,X2,X3)
    | r3_orders_2(X1,X4,esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_8]),
    [final]).

cnf(c_0_43,plain,
    ( esk1_3(X1,X2,X3) = k2_yellow_0(X1,X4)
    | r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk2_3(X1,esk1_3(X1,X2,X3),X4))
    | ~ r1_lattice3(X1,X4,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_8]),
    [final]).

cnf(c_0_44,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X3,esk2_3(X2,X1,X3))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_45,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X3,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,esk2_3(X1,esk1_3(X1,X3,X4),X2))
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_8]),
    [final]).

cnf(c_0_46,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,esk2_3(X1,X3,X2))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk2_3(esk3_0,X1,X2))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(esk2_3(esk3_0,X1,X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(esk1_3(esk3_0,X1,X2),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk2_3(esk3_0,X2,X1))
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(esk2_3(esk3_0,X2,X1),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk4_0)
    | ~ r2_hidden(esk4_0,X3)
    | ~ r1_lattice3(esk3_0,X3,esk2_3(esk3_0,X1,X2))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk5_0)
    | ~ r2_hidden(esk5_0,X3)
    | ~ r1_lattice3(esk3_0,X3,esk2_3(esk3_0,X1,X2))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_21]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk4_0)
    | ~ r2_hidden(esk4_0,X3)
    | ~ r1_lattice3(esk3_0,X3,esk2_3(esk3_0,X2,X1))
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_22]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk5_0)
    | ~ r2_hidden(esk5_0,X3)
    | ~ r1_lattice3(esk3_0,X3,esk2_3(esk3_0,X2,X1))
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_22]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r3_orders_2(esk3_0,X1,esk4_0)
    | ~ r1_orders_2(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_26]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( r3_orders_2(esk3_0,X1,esk5_0)
    | ~ r1_orders_2(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_16]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_56,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk4_0)
    | ~ r3_orders_2(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_26]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r3_orders_2(esk3_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_26]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk5_0)
    | ~ r3_orders_2(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( r3_orders_2(esk3_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_16]),
    [final]).

cnf(c_0_62,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | X4 = k2_yellow_0(X2,X5)
    | r3_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X4,X5))
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X5,X4)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X4,X5))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21]),
    [final]).

cnf(c_0_63,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r2_yellow_0(X2,X4)
    | r3_orders_2(X2,esk2_3(X2,X5,X4),esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_lattice3(X2,X4,X5)
    | ~ r1_orders_2(X2,esk2_3(X2,X5,X4),esk2_3(X2,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_22]),
    [final]).

cnf(c_0_64,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r2_yellow_0(X2,X4)
    | r3_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X5,X4))
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X4,X5)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X5,X4))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_21]),
    [final]).

cnf(c_0_65,plain,
    ( r2_yellow_0(X1,X2)
    | r2_yellow_0(X1,X3)
    | r3_orders_2(X1,esk2_3(X1,X4,X2),esk2_3(X1,X5,X3))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,X5)
    | ~ r1_lattice3(X1,X2,X4)
    | ~ r1_orders_2(X1,esk2_3(X1,X4,X2),esk2_3(X1,X5,X3))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22]),
    [final]).

cnf(c_0_66,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X4,X5)
    | r3_orders_2(X2,esk1_3(X2,X4,X5),esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,esk1_3(X2,X4,X5),esk2_3(X2,X1,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_8]),
    [final]).

cnf(c_0_67,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X4,X5)
    | r3_orders_2(X2,esk2_3(X2,X1,X3),esk1_3(X2,X4,X5))
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,esk2_3(X2,X1,X3),esk1_3(X2,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21]),
    [final]).

cnf(c_0_68,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X3,X4)
    | r3_orders_2(X1,esk1_3(X1,X3,X4),esk2_3(X1,X5,X2))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X5)
    | ~ r1_orders_2(X1,esk1_3(X1,X3,X4),esk2_3(X1,X5,X2))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_8]),
    [final]).

cnf(c_0_69,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X3,X4)
    | r3_orders_2(X1,esk2_3(X1,X5,X2),esk1_3(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X5)
    | ~ r1_orders_2(X1,esk2_3(X1,X5,X2),esk1_3(X1,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22]),
    [final]).

cnf(c_0_70,plain,
    ( esk1_3(X1,X2,X3) = k2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_8]),
    [final]).

cnf(c_0_71,plain,
    ( r1_lattice3(X1,X2,X3)
    | r1_lattice3(X1,X4,X5)
    | r3_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X4,X5))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_8]),
    [final]).

cnf(c_0_72,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_8]),
    [final]).

cnf(c_0_73,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_orders_2(X2,X4,esk2_3(X2,X1,X3))
    | ~ v5_orders_2(X2)
    | ~ r2_hidden(esk2_3(X2,X1,X3),X5)
    | ~ r1_lattice3(X2,X5,X4)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_21]),
    [final]).

cnf(c_0_74,plain,
    ( r1_lattice3(X1,X2,X3)
    | r1_lattice3(X1,X4,X5)
    | r1_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X4,X5))
    | ~ r1_lattice3(X1,X4,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_8]),
    [final]).

cnf(c_0_75,plain,
    ( r2_yellow_0(X1,X2)
    | r1_orders_2(X1,X3,esk2_3(X1,X4,X2))
    | ~ v5_orders_2(X1)
    | ~ r2_hidden(esk2_3(X1,X4,X2),X5)
    | ~ r1_lattice3(X1,X5,X3)
    | ~ r1_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_22]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,X1,X2))
    | ~ r1_lattice3(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_17])]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,X1,X2))
    | ~ r1_lattice3(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17])]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk2_3(esk3_0,X1,X2))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_21]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_8]),c_0_17])]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk2_3(esk3_0,X2,X1))
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_22]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk4_0)
    | ~ r2_hidden(esk4_0,X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_44]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk5_0)
    | ~ r2_hidden(esk5_0,X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r3_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X1,X2))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_25]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r3_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X1,X2))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_16]),c_0_25]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk4_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk5_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r3_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X2,X1))
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_25]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r3_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X2,X1))
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_16]),c_0_25]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r3_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,X1,X2))
    | ~ r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r3_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,X1,X2))
    | ~ r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_16]),c_0_17]),c_0_18])]),c_0_19]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk4_0)
    | ~ r2_hidden(esk4_0,X3)
    | ~ r1_lattice3(esk3_0,X3,esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_8]),c_0_17])]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk5_0)
    | ~ r2_hidden(esk5_0,X3)
    | ~ r1_lattice3(esk3_0,X3,esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_8]),c_0_17])]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r3_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk4_0)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_21]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( X1 = k2_yellow_0(esk3_0,X2)
    | r3_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk5_0)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_21]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r3_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk4_0)
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_96,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | r3_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk5_0)
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_25]),c_0_17])]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk4_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ r1_lattice3(esk3_0,X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_16]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk5_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ r1_lattice3(esk3_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26]),
    [final]).

cnf(c_0_99,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r3_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk4_0)
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_8]),c_0_17])]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,X2)
    | r3_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk5_0)
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_8]),c_0_17])]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( r3_orders_2(esk3_0,esk5_0,esk4_0)
    | ~ r1_orders_2(esk3_0,esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_16]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( r3_orders_2(esk3_0,esk4_0,esk5_0)
    | ~ r1_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_26]),
    [final]).

cnf(c_0_103,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ m1_subset_1(k2_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_56]),
    [final]).

cnf(c_0_104,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_57]),
    [final]).

cnf(c_0_105,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_107,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_26])]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_16])]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( k6_waybel_0(esk3_0,esk4_0) = k6_waybel_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:42:47 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  # Version: 2.5pre002
% 0.18/0.34  # No SInE strategy applied
% 0.18/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.18/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.028 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # No proof found!
% 0.18/0.38  # SZS status CounterSatisfiable
% 0.18/0.38  # SZS output start Saturation
% 0.18/0.38  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.18/0.38  fof(t20_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k6_waybel_0(X1,X2)=k6_waybel_0(X1,X3)=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_waybel_0)).
% 0.18/0.38  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.18/0.38  fof(t31_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3))=>(r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2)))))&((r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2))))=>(X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_yellow_0)).
% 0.18/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.18/0.38  fof(c_0_5, plain, ![X11, X12, X13, X14]:((~r1_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X12)|r1_orders_2(X11,X13,X14)))|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&((m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X11))|r1_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&((r2_hidden(esk1_3(X11,X12,X13),X12)|r1_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&(~r1_orders_2(X11,X13,esk1_3(X11,X12,X13))|r1_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.18/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k6_waybel_0(X1,X2)=k6_waybel_0(X1,X3)=>X2=X3))))), inference(assume_negation,[status(cth)],[t20_waybel_0])).
% 0.18/0.38  cnf(c_0_7, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.18/0.38  cnf(c_0_8, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.18/0.38  fof(c_0_9, plain, ![X8, X9, X10]:(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))|r3_orders_2(X8,X9,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.18/0.38  fof(c_0_10, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(k6_waybel_0(esk3_0,esk4_0)=k6_waybel_0(esk3_0,esk5_0)&esk4_0!=esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.18/0.38  cnf(c_0_11, plain, (r1_lattice3(X1,X2,X3)|r1_orders_2(X1,X4,esk1_3(X1,X2,X3))|~r2_hidden(esk1_3(X1,X2,X3),X5)|~r1_lattice3(X1,X5,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_7, c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_12, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.18/0.38  fof(c_0_13, plain, ![X16, X17, X18, X19, X20]:(((r1_lattice3(X16,X18,X17)|(X17!=k2_yellow_0(X16,X18)|~r2_yellow_0(X16,X18))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(~m1_subset_1(X19,u1_struct_0(X16))|(~r1_lattice3(X16,X18,X19)|r1_orders_2(X16,X19,X17))|(X17!=k2_yellow_0(X16,X18)|~r2_yellow_0(X16,X18))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))&(((X17=k2_yellow_0(X16,X20)|(m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(r2_yellow_0(X16,X20)|(m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))&(((X17=k2_yellow_0(X16,X20)|(r1_lattice3(X16,X20,esk2_3(X16,X17,X20))|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(r2_yellow_0(X16,X20)|(r1_lattice3(X16,X20,esk2_3(X16,X17,X20))|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))&((X17=k2_yellow_0(X16,X20)|(~r1_orders_2(X16,esk2_3(X16,X17,X20),X17)|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(r2_yellow_0(X16,X20)|(~r1_orders_2(X16,esk2_3(X16,X17,X20),X17)|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).
% 0.18/0.38  fof(c_0_14, plain, ![X5, X6, X7]:((~r3_orders_2(X5,X6,X7)|r1_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))&(~r1_orders_2(X5,X6,X7)|r3_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.18/0.38  cnf(c_0_15, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.38  cnf(c_0_17, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.38  cnf(c_0_18, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.38  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.38  cnf(c_0_20, plain, (r1_lattice3(X1,X2,X3)|r1_orders_2(X1,X4,esk1_3(X1,X2,X3))|~r1_lattice3(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.18/0.38  cnf(c_0_21, plain, (X1=k2_yellow_0(X2,X3)|m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.38  cnf(c_0_22, plain, (r2_yellow_0(X1,X2)|m1_subset_1(esk2_3(X1,X3,X2),u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.38  cnf(c_0_23, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.38  cnf(c_0_24, negated_conjecture, (r3_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_25, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.38  cnf(c_0_27, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.18/0.38  cnf(c_0_28, plain, (X1=k2_yellow_0(X2,X3)|~r1_orders_2(X2,esk2_3(X2,X1,X3),X1)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.38  cnf(c_0_29, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X4,X5)|r1_orders_2(X2,esk2_3(X2,X1,X3),esk1_3(X2,X4,X5))|~v5_orders_2(X2)|~r1_lattice3(X2,X4,esk2_3(X2,X1,X3))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 0.18/0.38  cnf(c_0_30, plain, (r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk2_3(X1,X3,X2),X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.38  cnf(c_0_31, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X1,X3,X4)|r1_orders_2(X1,esk2_3(X1,X5,X2),esk1_3(X1,X3,X4))|~v5_orders_2(X1)|~r1_lattice3(X1,X3,esk2_3(X1,X5,X2))|~r1_lattice3(X1,X2,X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_20, c_0_22]), ['final']).
% 0.18/0.38  cnf(c_0_32, plain, (X1=k2_yellow_0(X2,X3)|r1_orders_2(X2,X4,esk2_3(X2,X1,X3))|v2_struct_0(X2)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~r3_orders_2(X2,X4,esk2_3(X2,X1,X3))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_23, c_0_21]), ['final']).
% 0.18/0.38  cnf(c_0_33, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r3_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk2_3(esk3_0,X1,X2))|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_34, plain, (r1_lattice3(X1,X2,X3)|r1_orders_2(X1,X4,esk1_3(X1,X2,X3))|v2_struct_0(X1)|~r3_orders_2(X1,X4,esk1_3(X1,X2,X3))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_23, c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_35, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r3_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk1_3(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_8]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_36, plain, (r2_yellow_0(X1,X2)|r1_orders_2(X1,X3,esk2_3(X1,X4,X2))|v2_struct_0(X1)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X4)|~r3_orders_2(X1,X3,esk2_3(X1,X4,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_23, c_0_22]), ['final']).
% 0.18/0.38  cnf(c_0_37, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r3_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk2_3(esk3_0,X2,X1))|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk3_0,X1,esk4_0)|~r2_hidden(esk4_0,X2)|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_26]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_39, negated_conjecture, (r1_orders_2(esk3_0,X1,esk5_0)|~r2_hidden(esk5_0,X2)|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_16]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_40, plain, (X1=k2_yellow_0(X2,X3)|r3_orders_2(X2,X4,esk2_3(X2,X1,X3))|v2_struct_0(X2)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~r1_orders_2(X2,X4,esk2_3(X2,X1,X3))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_27, c_0_21]), ['final']).
% 0.18/0.38  cnf(c_0_41, plain, (r2_yellow_0(X1,X2)|r3_orders_2(X1,X3,esk2_3(X1,X4,X2))|v2_struct_0(X1)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X4)|~r1_orders_2(X1,X3,esk2_3(X1,X4,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_27, c_0_22]), ['final']).
% 0.18/0.38  cnf(c_0_42, plain, (r1_lattice3(X1,X2,X3)|r3_orders_2(X1,X4,esk1_3(X1,X2,X3))|v2_struct_0(X1)|~r1_orders_2(X1,X4,esk1_3(X1,X2,X3))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_27, c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_43, plain, (esk1_3(X1,X2,X3)=k2_yellow_0(X1,X4)|r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,esk2_3(X1,esk1_3(X1,X2,X3),X4))|~r1_lattice3(X1,X4,esk1_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_44, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X3,esk2_3(X2,X1,X3))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.38  cnf(c_0_45, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X1,X3,X4)|~v5_orders_2(X1)|~r1_lattice3(X1,X3,esk2_3(X1,esk1_3(X1,X3,X4),X2))|~r1_lattice3(X1,X2,esk1_3(X1,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_46, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X1,X2,esk2_3(X1,X3,X2))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.38  cnf(c_0_47, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk2_3(esk3_0,X1,X2))|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(esk2_3(esk3_0,X1,X2),u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_17]), c_0_18])]), c_0_19])).
% 0.18/0.38  cnf(c_0_48, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk1_3(esk3_0,X1,X2))|~m1_subset_1(esk1_3(esk3_0,X1,X2),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_17]), c_0_18])]), c_0_19])).
% 0.18/0.38  cnf(c_0_49, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk2_3(esk3_0,X2,X1))|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(esk2_3(esk3_0,X2,X1),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_25]), c_0_17]), c_0_18])]), c_0_19])).
% 0.18/0.38  cnf(c_0_50, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk4_0)|~r2_hidden(esk4_0,X3)|~r1_lattice3(esk3_0,X3,esk2_3(esk3_0,X1,X2))|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_21]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_51, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk5_0)|~r2_hidden(esk5_0,X3)|~r1_lattice3(esk3_0,X3,esk2_3(esk3_0,X1,X2))|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_21]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_52, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk4_0)|~r2_hidden(esk4_0,X3)|~r1_lattice3(esk3_0,X3,esk2_3(esk3_0,X2,X1))|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_22]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_53, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk5_0)|~r2_hidden(esk5_0,X3)|~r1_lattice3(esk3_0,X3,esk2_3(esk3_0,X2,X1))|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_22]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_54, negated_conjecture, (r3_orders_2(esk3_0,X1,esk4_0)|~r1_orders_2(esk3_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_26]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_55, negated_conjecture, (r3_orders_2(esk3_0,X1,esk5_0)|~r1_orders_2(esk3_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_16]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_56, plain, (r1_orders_2(X2,X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.38  cnf(c_0_57, plain, (r1_lattice3(X1,X2,X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.38  cnf(c_0_58, negated_conjecture, (r1_orders_2(esk3_0,X1,esk4_0)|~r3_orders_2(esk3_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_26]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_59, negated_conjecture, (r3_orders_2(esk3_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_26]), ['final']).
% 0.18/0.38  cnf(c_0_60, negated_conjecture, (r1_orders_2(esk3_0,X1,esk5_0)|~r3_orders_2(esk3_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_16]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_61, negated_conjecture, (r3_orders_2(esk3_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_16]), ['final']).
% 0.18/0.38  cnf(c_0_62, plain, (X1=k2_yellow_0(X2,X3)|X4=k2_yellow_0(X2,X5)|r3_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X4,X5))|v2_struct_0(X2)|~v5_orders_2(X2)|~r1_lattice3(X2,X5,X4)|~r1_lattice3(X2,X3,X1)|~r1_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X4,X5))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_40, c_0_21]), ['final']).
% 0.18/0.38  cnf(c_0_63, plain, (X1=k2_yellow_0(X2,X3)|r2_yellow_0(X2,X4)|r3_orders_2(X2,esk2_3(X2,X5,X4),esk2_3(X2,X1,X3))|v2_struct_0(X2)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~r1_lattice3(X2,X4,X5)|~r1_orders_2(X2,esk2_3(X2,X5,X4),esk2_3(X2,X1,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X5,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_40, c_0_22]), ['final']).
% 0.18/0.38  cnf(c_0_64, plain, (X1=k2_yellow_0(X2,X3)|r2_yellow_0(X2,X4)|r3_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X5,X4))|v2_struct_0(X2)|~v5_orders_2(X2)|~r1_lattice3(X2,X4,X5)|~r1_lattice3(X2,X3,X1)|~r1_orders_2(X2,esk2_3(X2,X1,X3),esk2_3(X2,X5,X4))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_41, c_0_21]), ['final']).
% 0.18/0.38  cnf(c_0_65, plain, (r2_yellow_0(X1,X2)|r2_yellow_0(X1,X3)|r3_orders_2(X1,esk2_3(X1,X4,X2),esk2_3(X1,X5,X3))|v2_struct_0(X1)|~v5_orders_2(X1)|~r1_lattice3(X1,X3,X5)|~r1_lattice3(X1,X2,X4)|~r1_orders_2(X1,esk2_3(X1,X4,X2),esk2_3(X1,X5,X3))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_22]), ['final']).
% 0.18/0.38  cnf(c_0_66, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X4,X5)|r3_orders_2(X2,esk1_3(X2,X4,X5),esk2_3(X2,X1,X3))|v2_struct_0(X2)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~r1_orders_2(X2,esk1_3(X2,X4,X5),esk2_3(X2,X1,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X5,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_40, c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_67, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X4,X5)|r3_orders_2(X2,esk2_3(X2,X1,X3),esk1_3(X2,X4,X5))|v2_struct_0(X2)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~r1_orders_2(X2,esk2_3(X2,X1,X3),esk1_3(X2,X4,X5))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_42, c_0_21]), ['final']).
% 0.18/0.38  cnf(c_0_68, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X1,X3,X4)|r3_orders_2(X1,esk1_3(X1,X3,X4),esk2_3(X1,X5,X2))|v2_struct_0(X1)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X5)|~r1_orders_2(X1,esk1_3(X1,X3,X4),esk2_3(X1,X5,X2))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_69, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X1,X3,X4)|r3_orders_2(X1,esk2_3(X1,X5,X2),esk1_3(X1,X3,X4))|v2_struct_0(X1)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X5)|~r1_orders_2(X1,esk2_3(X1,X5,X2),esk1_3(X1,X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_42, c_0_22]), ['final']).
% 0.18/0.38  cnf(c_0_70, plain, (esk1_3(X1,X2,X3)=k2_yellow_0(X1,X2)|r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_71, plain, (r1_lattice3(X1,X2,X3)|r1_lattice3(X1,X4,X5)|r3_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X4,X5))|v2_struct_0(X1)|~r1_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X4,X5))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_42, c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_72, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_73, plain, (X1=k2_yellow_0(X2,X3)|r1_orders_2(X2,X4,esk2_3(X2,X1,X3))|~v5_orders_2(X2)|~r2_hidden(esk2_3(X2,X1,X3),X5)|~r1_lattice3(X2,X5,X4)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_7, c_0_21]), ['final']).
% 0.18/0.38  cnf(c_0_74, plain, (r1_lattice3(X1,X2,X3)|r1_lattice3(X1,X4,X5)|r1_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X4,X5))|~r1_lattice3(X1,X4,esk1_3(X1,X2,X3))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_20, c_0_8]), ['final']).
% 0.18/0.38  cnf(c_0_75, plain, (r2_yellow_0(X1,X2)|r1_orders_2(X1,X3,esk2_3(X1,X4,X2))|~v5_orders_2(X1)|~r2_hidden(esk2_3(X1,X4,X2),X5)|~r1_lattice3(X1,X5,X3)|~r1_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_7, c_0_22]), ['final']).
% 0.18/0.38  cnf(c_0_76, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,X1,X2))|~r1_lattice3(esk3_0,X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_26]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_77, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,X1,X2))|~r1_lattice3(esk3_0,X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_78, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk2_3(esk3_0,X1,X2))|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_21]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_79, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk1_3(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_8]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_80, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk2_3(esk3_0,X2,X1))|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_22]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_81, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk4_0)|~r2_hidden(esk4_0,X2)|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_44]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_82, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk5_0)|~r2_hidden(esk5_0,X2)|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_44]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_83, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r3_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X1,X2))|~r1_lattice3(esk3_0,X2,X1)|~r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X1,X2))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_26]), c_0_25]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_84, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r3_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X1,X2))|~r1_lattice3(esk3_0,X2,X1)|~r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X1,X2))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_16]), c_0_25]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_85, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk4_0)|~r2_hidden(esk4_0,X1)|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_46]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_86, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk5_0)|~r2_hidden(esk5_0,X1)|~r1_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_46]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_87, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r3_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X2,X1))|~r1_lattice3(esk3_0,X1,X2)|~r1_orders_2(esk3_0,esk4_0,esk2_3(esk3_0,X2,X1))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_25]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_88, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r3_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X2,X1))|~r1_lattice3(esk3_0,X1,X2)|~r1_orders_2(esk3_0,esk5_0,esk2_3(esk3_0,X2,X1))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_16]), c_0_25]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_89, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r3_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,X1,X2))|~r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_90, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r3_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,X1,X2))|~r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_16]), c_0_17]), c_0_18])]), c_0_19]), ['final']).
% 0.18/0.38  cnf(c_0_91, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk4_0)|~r2_hidden(esk4_0,X3)|~r1_lattice3(esk3_0,X3,esk1_3(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_8]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_92, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk5_0)|~r2_hidden(esk5_0,X3)|~r1_lattice3(esk3_0,X3,esk1_3(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_8]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_93, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r3_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk4_0)|~r1_lattice3(esk3_0,X2,X1)|~r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_21]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_94, negated_conjecture, (X1=k2_yellow_0(esk3_0,X2)|r3_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk5_0)|~r1_lattice3(esk3_0,X2,X1)|~r1_orders_2(esk3_0,esk2_3(esk3_0,X1,X2),esk5_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_21]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_95, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r3_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk4_0)|~r1_lattice3(esk3_0,X1,X2)|~r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk4_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_22]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_96, negated_conjecture, (r2_yellow_0(esk3_0,X1)|r3_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk5_0)|~r1_lattice3(esk3_0,X1,X2)|~r1_orders_2(esk3_0,esk2_3(esk3_0,X2,X1),esk5_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_22]), c_0_25]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_97, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk4_0)|~r2_hidden(esk4_0,X1)|~r1_lattice3(esk3_0,X1,esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_16]), ['final']).
% 0.18/0.38  cnf(c_0_98, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk5_0)|~r2_hidden(esk5_0,X1)|~r1_lattice3(esk3_0,X1,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_26]), ['final']).
% 0.18/0.38  cnf(c_0_99, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r3_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk4_0)|~r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk4_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_8]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_100, negated_conjecture, (r1_lattice3(esk3_0,X1,X2)|r3_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk5_0)|~r1_orders_2(esk3_0,esk1_3(esk3_0,X1,X2),esk5_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_8]), c_0_17])]), ['final']).
% 0.18/0.38  cnf(c_0_101, negated_conjecture, (r3_orders_2(esk3_0,esk5_0,esk4_0)|~r1_orders_2(esk3_0,esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_16]), ['final']).
% 0.18/0.38  cnf(c_0_102, negated_conjecture, (r3_orders_2(esk3_0,esk4_0,esk5_0)|~r1_orders_2(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_55, c_0_26]), ['final']).
% 0.18/0.38  cnf(c_0_103, plain, (r1_orders_2(X1,X2,k2_yellow_0(X1,X3))|~r2_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_lattice3(X1,X3,X2)|~m1_subset_1(k2_yellow_0(X1,X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_56]), ['final']).
% 0.18/0.38  cnf(c_0_104, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_57]), ['final']).
% 0.18/0.38  cnf(c_0_105, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.18/0.38  cnf(c_0_106, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.38  cnf(c_0_107, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_26])]), ['final']).
% 0.18/0.38  cnf(c_0_108, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_16])]), ['final']).
% 0.18/0.38  cnf(c_0_109, negated_conjecture, (k6_waybel_0(esk3_0,esk4_0)=k6_waybel_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.18/0.38  # SZS output end Saturation
% 0.18/0.38  # Proof object total steps             : 110
% 0.18/0.38  # Proof object clause steps            : 99
% 0.18/0.38  # Proof object formula steps           : 11
% 0.18/0.38  # Proof object conjectures             : 59
% 0.18/0.38  # Proof object clause conjectures      : 56
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 23
% 0.18/0.38  # Proof object initial formulas used   : 5
% 0.18/0.38  # Proof object generating inferences   : 74
% 0.18/0.38  # Proof object simplifying inferences  : 140
% 0.18/0.38  # Parsed axioms                        : 5
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 23
% 0.18/0.38  # Removed in clause preprocessing      : 0
% 0.18/0.38  # Initial clauses in saturation        : 23
% 0.18/0.38  # Processed clauses                    : 136
% 0.18/0.38  # ...of these trivial                  : 0
% 0.18/0.38  # ...subsumed                          : 14
% 0.18/0.38  # ...remaining for further processing  : 122
% 0.18/0.38  # Other redundant clauses eliminated   : 2
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 3
% 0.18/0.38  # Backward-rewritten                   : 0
% 0.18/0.38  # Generated clauses                    : 134
% 0.18/0.38  # ...of the previous two non-trivial   : 92
% 0.18/0.38  # Contextual simplify-reflections      : 4
% 0.18/0.38  # Paramodulations                      : 132
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 2
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 94
% 0.18/0.38  #    Positive orientable unit clauses  : 10
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 2
% 0.18/0.38  #    Non-unit-clauses                  : 82
% 0.18/0.38  # Current number of unprocessed clauses: 0
% 0.18/0.38  # ...number of literals in the above   : 0
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 26
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 2774
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 316
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 21
% 0.18/0.38  # Unit Clause-clause subsumption calls : 8
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 2
% 0.18/0.38  # BW rewrite match successes           : 0
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 7743
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.040 s
% 0.18/0.38  # System time              : 0.006 s
% 0.18/0.38  # Total time               : 0.046 s
% 0.18/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
