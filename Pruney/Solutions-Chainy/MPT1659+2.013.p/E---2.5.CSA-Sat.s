%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:24 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 115 expanded)
%              Number of clauses        :   34 (  43 expanded)
%              Number of leaves         :    5 (  31 expanded)
%              Depth                    :    5
%              Number of atoms          :  329 (1438 expanded)
%              Number of equality atoms :   25 ( 133 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t39_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_yellow_0(X1,k6_waybel_0(X1,X2))
            & k2_yellow_0(X1,k6_waybel_0(X1,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_waybel_0)).

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

fof(c_0_5,plain,(
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

fof(c_0_6,plain,(
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

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r2_yellow_0(X1,k6_waybel_0(X1,X2))
              & k2_yellow_0(X1,k6_waybel_0(X1,X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_waybel_0])).

cnf(c_0_8,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X3,esk2_3(X2,X1,X3))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_10,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_11,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_12,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,esk2_3(X1,X3,X2))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_13,plain,
    ( r2_yellow_0(X1,X2)
    | m1_subset_1(esk2_3(X1,X3,X2),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

fof(c_0_14,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v3_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | r3_orders_2(X8,X9,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ( ~ r2_yellow_0(esk3_0,k6_waybel_0(esk3_0,esk4_0))
      | k2_yellow_0(esk3_0,k6_waybel_0(esk3_0,esk4_0)) != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_16,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_17,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_orders_2(X2,esk2_3(X2,X1,X3),X4)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),
    [final]).

cnf(c_0_18,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_orders_2(X2,esk2_3(X2,X1,X3),X4)
    | ~ v5_orders_2(X2)
    | ~ r2_hidden(X4,X3)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_9]),c_0_10]),
    [final]).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_20,plain,
    ( r2_yellow_0(X1,X2)
    | r1_orders_2(X1,esk2_3(X1,X3,X2),X4)
    | ~ v5_orders_2(X1)
    | ~ r2_hidden(X4,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),
    [final]).

fof(c_0_21,plain,(
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

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_27,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X4,esk2_3(X2,X1,X3))
    | esk1_3(X2,X4,esk2_3(X2,X1,X3)) != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(esk1_3(X2,X4,esk2_3(X2,X1,X3)),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_10])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_29,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,esk2_3(X2,X1,X3),X1)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_30,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X4,X3,X5)
    | r1_orders_2(X2,esk2_3(X2,X1,X3),esk1_3(X4,X3,X5))
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(esk1_3(X4,X3,X5),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

cnf(c_0_31,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk2_3(X1,X3,X2),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_32,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X3,X2,X4)
    | r1_orders_2(X1,esk2_3(X1,X5,X2),esk1_3(X3,X2,X4))
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,X5)
    | ~ m1_subset_1(esk1_3(X3,X2,X4),u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19]),
    [final]).

cnf(c_0_33,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r3_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26]),
    [final]).

cnf(c_0_36,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X4,esk2_3(X2,X1,X3))
    | esk1_3(X2,X4,esk2_3(X2,X1,X3)) != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_10]),
    [final]).

cnf(c_0_37,plain,
    ( esk1_3(X1,X2,X3) = k2_yellow_0(X4,X2)
    | r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X4)
    | ~ r1_lattice3(X4,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30]),
    [final]).

cnf(c_0_38,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X3,X2,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_lattice3(X1,X2,esk1_3(X3,X2,X4))
    | ~ m1_subset_1(esk1_3(X3,X2,X4),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32]),
    [final]).

cnf(c_0_39,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24]),c_0_25])]),c_0_26]),
    [final]).

cnf(c_0_41,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_yellow_0(esk3_0,k6_waybel_0(esk3_0,esk4_0))
    | k2_yellow_0(esk3_0,k6_waybel_0(esk3_0,esk4_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(t31_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3))=>(r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2)))))&((r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2))))=>(X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_yellow_0)).
% 0.13/0.38  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.13/0.38  fof(t39_waybel_0, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_yellow_0(X1,k6_waybel_0(X1,X2))&k2_yellow_0(X1,k6_waybel_0(X1,X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_waybel_0)).
% 0.13/0.38  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.13/0.38  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.13/0.38  fof(c_0_5, plain, ![X16, X17, X18, X19, X20]:(((r1_lattice3(X16,X18,X17)|(X17!=k2_yellow_0(X16,X18)|~r2_yellow_0(X16,X18))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(~m1_subset_1(X19,u1_struct_0(X16))|(~r1_lattice3(X16,X18,X19)|r1_orders_2(X16,X19,X17))|(X17!=k2_yellow_0(X16,X18)|~r2_yellow_0(X16,X18))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))&(((X17=k2_yellow_0(X16,X20)|(m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(r2_yellow_0(X16,X20)|(m1_subset_1(esk2_3(X16,X17,X20),u1_struct_0(X16))|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))&(((X17=k2_yellow_0(X16,X20)|(r1_lattice3(X16,X20,esk2_3(X16,X17,X20))|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(r2_yellow_0(X16,X20)|(r1_lattice3(X16,X20,esk2_3(X16,X17,X20))|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))&((X17=k2_yellow_0(X16,X20)|(~r1_orders_2(X16,esk2_3(X16,X17,X20),X17)|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16)))&(r2_yellow_0(X16,X20)|(~r1_orders_2(X16,esk2_3(X16,X17,X20),X17)|~r1_lattice3(X16,X20,X17))|~m1_subset_1(X17,u1_struct_0(X16))|(~v5_orders_2(X16)|~l1_orders_2(X16))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X11, X12, X13, X14]:((~r1_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X12)|r1_orders_2(X11,X13,X14)))|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&((m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X11))|r1_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&((r2_hidden(esk1_3(X11,X12,X13),X12)|r1_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&(~r1_orders_2(X11,X13,esk1_3(X11,X12,X13))|r1_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.13/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_yellow_0(X1,k6_waybel_0(X1,X2))&k2_yellow_0(X1,k6_waybel_0(X1,X2))=X2)))), inference(assume_negation,[status(cth)],[t39_waybel_0])).
% 0.13/0.38  cnf(c_0_8, plain, (r1_orders_2(X2,X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_9, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X3,esk2_3(X2,X1,X3))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_10, plain, (X1=k2_yellow_0(X2,X3)|m1_subset_1(esk2_3(X2,X1,X3),u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_11, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_12, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X1,X2,esk2_3(X1,X3,X2))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_13, plain, (r2_yellow_0(X1,X2)|m1_subset_1(esk2_3(X1,X3,X2),u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  fof(c_0_14, plain, ![X8, X9, X10]:(v2_struct_0(X8)|~v3_orders_2(X8)|~l1_orders_2(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))|r3_orders_2(X8,X9,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(~r2_yellow_0(esk3_0,k6_waybel_0(esk3_0,esk4_0))|k2_yellow_0(esk3_0,k6_waybel_0(esk3_0,esk4_0))!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_17, plain, (X1=k2_yellow_0(X2,X3)|r1_orders_2(X2,esk2_3(X2,X1,X3),X4)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_18, plain, (X1=k2_yellow_0(X2,X3)|r1_orders_2(X2,esk2_3(X2,X1,X3),X4)|~v5_orders_2(X2)|~r2_hidden(X4,X3)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_9]), c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_20, plain, (r2_yellow_0(X1,X2)|r1_orders_2(X1,esk2_3(X1,X3,X2),X4)|~v5_orders_2(X1)|~r2_hidden(X4,X2)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), ['final']).
% 0.13/0.38  fof(c_0_21, plain, ![X5, X6, X7]:((~r3_orders_2(X5,X6,X7)|r1_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))&(~r1_orders_2(X5,X6,X7)|r3_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.13/0.38  cnf(c_0_22, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_27, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X4,esk2_3(X2,X1,X3))|esk1_3(X2,X4,esk2_3(X2,X1,X3))!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(esk1_3(X2,X4,esk2_3(X2,X1,X3)),u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_10])).
% 0.13/0.38  cnf(c_0_28, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_29, plain, (X1=k2_yellow_0(X2,X3)|~r1_orders_2(X2,esk2_3(X2,X1,X3),X1)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_30, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X4,X3,X5)|r1_orders_2(X2,esk2_3(X2,X1,X3),esk1_3(X4,X3,X5))|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(esk1_3(X4,X3,X5),u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X5,u1_struct_0(X4))|~l1_orders_2(X2)|~l1_orders_2(X4)), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.13/0.38  cnf(c_0_31, plain, (r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk2_3(X1,X3,X2),X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_32, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X3,X2,X4)|r1_orders_2(X1,esk2_3(X1,X5,X2),esk1_3(X3,X2,X4))|~v5_orders_2(X1)|~r1_lattice3(X1,X2,X5)|~m1_subset_1(esk1_3(X3,X2,X4),u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X3))|~l1_orders_2(X1)|~l1_orders_2(X3)), inference(spm,[status(thm)],[c_0_20, c_0_19]), ['final']).
% 0.13/0.38  cnf(c_0_33, plain, (r1_lattice3(X1,X2,X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  cnf(c_0_34, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r3_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])]), c_0_26]), ['final']).
% 0.13/0.38  cnf(c_0_36, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X4,esk2_3(X2,X1,X3))|esk1_3(X2,X4,esk2_3(X2,X1,X3))!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~v5_orders_2(X2)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_10]), ['final']).
% 0.13/0.38  cnf(c_0_37, plain, (esk1_3(X1,X2,X3)=k2_yellow_0(X4,X2)|r1_lattice3(X1,X2,X3)|~v5_orders_2(X4)|~r1_lattice3(X4,X2,esk1_3(X1,X2,X3))|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X4)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30]), ['final']).
% 0.13/0.38  cnf(c_0_38, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X3,X2,X4)|~v5_orders_2(X1)|~r1_lattice3(X1,X2,esk1_3(X3,X2,X4))|~m1_subset_1(esk1_3(X3,X2,X4),u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X3))|~l1_orders_2(X1)|~l1_orders_2(X3)), inference(spm,[status(thm)],[c_0_31, c_0_32]), ['final']).
% 0.13/0.38  cnf(c_0_39, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_33]), ['final']).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r1_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_24]), c_0_25])]), c_0_26]), ['final']).
% 0.13/0.38  cnf(c_0_41, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (~r2_yellow_0(esk3_0,k6_waybel_0(esk3_0,esk4_0))|k2_yellow_0(esk3_0,k6_waybel_0(esk3_0,esk4_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 45
% 0.13/0.38  # Proof object clause steps            : 34
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 22
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 12
% 0.13/0.38  # Proof object simplifying inferences  : 13
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 22
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 22
% 0.13/0.38  # Processed clauses                    : 63
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 7
% 0.13/0.38  # ...remaining for further processing  : 56
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 23
% 0.13/0.38  # ...of the previous two non-trivial   : 19
% 0.13/0.38  # Contextual simplify-reflections      : 5
% 0.13/0.38  # Paramodulations                      : 22
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 33
% 0.13/0.38  #    Positive orientable unit clauses  : 5
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 27
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 23
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 840
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 51
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3283
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
