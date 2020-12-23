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
% DateTime   : Thu Dec  3 11:16:19 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 503 expanded)
%              Number of clauses        :   60 ( 208 expanded)
%              Number of leaves         :    5 ( 144 expanded)
%              Depth                    :    6
%              Number of atoms          :  471 (6259 expanded)
%              Number of equality atoms :   36 ( 363 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   32 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(t15_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(t34_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
            & k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(c_0_5,plain,(
    ! [X12,X13,X14,X15] :
      ( ( r2_lattice3(X12,X13,X14)
        | X14 != k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_lattice3(X12,X13,X15)
        | r1_orders_2(X12,X14,X15)
        | X14 != k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))
        | ~ r2_lattice3(X12,X13,X14)
        | X14 = k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( r2_lattice3(X12,X13,esk2_3(X12,X13,X14))
        | ~ r2_lattice3(X12,X13,X14)
        | X14 = k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,X14,esk2_3(X12,X13,X14))
        | ~ r2_lattice3(X12,X13,X14)
        | X14 = k1_yellow_0(X12,X13)
        | ~ r1_yellow_0(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_6,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( m1_subset_1(esk3_2(X17,X18),u1_struct_0(X17))
        | ~ r1_yellow_0(X17,X18)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_lattice3(X17,X18,esk3_2(X17,X18))
        | ~ r1_yellow_0(X17,X18)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X18,X20)
        | r1_orders_2(X17,esk3_2(X17,X18),X20)
        | ~ r1_yellow_0(X17,X18)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk4_3(X17,X21,X22),u1_struct_0(X17))
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X21,X22)
        | r1_yellow_0(X17,X21)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_lattice3(X17,X21,esk4_3(X17,X21,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X21,X22)
        | r1_yellow_0(X17,X21)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X22,esk4_3(X17,X21,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X21,X22)
        | r1_yellow_0(X17,X21)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_hidden(X10,X8)
        | r1_orders_2(X7,X10,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))
        | r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,esk1_3(X7,X8,X9),X9)
        | r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_8,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,plain,
    ( r1_orders_2(X2,esk3_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_12,plain,
    ( r2_lattice3(X1,X2,esk3_2(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_14,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_15,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_16,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_17,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_18,plain,
    ( esk3_2(X1,X2) = k1_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,esk2_3(X1,X3,esk3_2(X1,X2)))
    | ~ r2_lattice3(X1,X3,esk3_2(X1,X2))
    | ~ m1_subset_1(esk2_3(X1,X3,esk3_2(X1,X2)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),
    [final]).

cnf(c_0_19,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_20,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X2,esk3_2(X1,X3))
    | X2 != k1_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_10]),
    [final]).

fof(c_0_22,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ v3_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | r1_orders_2(X5,X6,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
              & k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_waybel_0])).

cnf(c_0_24,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r1_orders_2(X2,X4,esk2_3(X2,X3,X1))
    | ~ r1_yellow_0(X2,X3)
    | ~ r2_hidden(X4,X3)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),
    [final]).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_26,plain,
    ( r1_yellow_0(X1,X2)
    | r1_orders_2(X1,X3,esk4_3(X1,X2,X4))
    | ~ v5_orders_2(X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_16]),c_0_17]),
    [final]).

cnf(c_0_27,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r1_orders_2(X2,X4,esk2_3(X2,X3,X1))
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_14]),c_0_15]),
    [final]).

cnf(c_0_28,plain,
    ( esk3_2(X1,X2) = k1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(esk2_3(X1,X2,esk3_2(X1,X2)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_10]),c_0_12])).

cnf(c_0_29,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_30,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X2,esk3_2(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_12]),c_0_10]),
    [final]).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,X2,esk3_2(X1,X3))
    | esk1_3(X1,X2,esk3_2(X1,X3)) != k1_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(esk1_3(X1,X2,esk3_2(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_10])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

fof(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ( ~ r1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk6_0))
      | k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk6_0)) != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

cnf(c_0_36,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X4,X3,X5)
    | r1_orders_2(X2,esk1_3(X4,X3,X5),esk2_3(X2,X3,X1))
    | ~ r1_yellow_0(X2,X3)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(esk1_3(X4,X3,X5),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X4) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_37,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X3,X2,X4)
    | r1_orders_2(X1,esk1_3(X3,X2,X4),esk4_3(X1,X2,X5))
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X5)
    | ~ m1_subset_1(esk1_3(X3,X2,X4),u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25]),
    [final]).

cnf(c_0_38,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X4,esk2_3(X2,X3,X1))
    | esk1_3(X2,X4,esk2_3(X2,X3,X1)) != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(esk1_3(X2,X4,esk2_3(X2,X3,X1)),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_27]),c_0_15])).

cnf(c_0_39,plain,
    ( esk3_2(X1,X2) = k1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_10]),c_0_12]),
    [final]).

cnf(c_0_40,plain,
    ( r1_orders_2(X1,X2,k1_yellow_0(X1,X3))
    | ~ r1_yellow_0(X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_29]),
    [final]).

cnf(c_0_41,plain,
    ( r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ r2_lattice3(X1,X3,esk4_3(X1,X2,esk3_2(X1,X3)))
    | ~ r2_lattice3(X1,X2,esk3_2(X1,X3))
    | ~ m1_subset_1(esk4_3(X1,X2,esk3_2(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_9]),c_0_10]),
    [final]).

cnf(c_0_42,plain,
    ( r2_lattice3(X1,X2,X3)
    | r1_orders_2(X4,esk1_3(X1,X2,X3),esk3_2(X4,X2))
    | ~ v5_orders_2(X4)
    | ~ r1_yellow_0(X4,X2)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25]),
    [final]).

cnf(c_0_43,plain,
    ( r2_lattice3(X1,X2,esk3_2(X1,X3))
    | esk1_3(X1,X2,esk3_2(X1,X3)) != k1_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_10]),
    [final]).

cnf(c_0_44,plain,
    ( r1_orders_2(X1,esk3_2(X1,X2),esk3_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_10]),
    [final]).

cnf(c_0_45,plain,
    ( r1_orders_2(X1,X2,k1_yellow_0(X1,X3))
    | X2 != k1_yellow_0(X1,X3)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_29]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_50,plain,
    ( esk1_3(X1,X2,X3) = k1_yellow_0(X4,X2)
    | r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X4,X2)
    | ~ r2_lattice3(X4,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_36]),
    [final]).

cnf(c_0_51,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X3,X2,X4)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,esk1_3(X3,X2,X4))
    | ~ m1_subset_1(esk1_3(X3,X2,X4),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37]),
    [final]).

cnf(c_0_52,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X4,esk2_3(X2,X3,X1))
    | esk1_3(X2,X4,esk2_3(X2,X3,X1)) != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_15]),
    [final]).

cnf(c_0_53,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,esk2_3(X1,X3,k1_yellow_0(X1,X2)))
    | ~ r2_lattice3(X1,X3,k1_yellow_0(X1,X2))
    | ~ m1_subset_1(esk2_3(X1,X3,k1_yellow_0(X1,X2)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_39]),
    [final]).

cnf(c_0_54,plain,
    ( r2_lattice3(X1,X2,X3)
    | r1_orders_2(X4,esk1_3(X1,X2,X3),k1_yellow_0(X4,X2))
    | ~ r1_yellow_0(X4,X2)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))
    | ~ m1_subset_1(k1_yellow_0(X4,X2),u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25]),
    [final]).

cnf(c_0_55,plain,
    ( r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ r2_lattice3(X1,X3,esk4_3(X1,X2,k1_yellow_0(X1,X3)))
    | ~ r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | ~ m1_subset_1(esk4_3(X1,X2,k1_yellow_0(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39]),
    [final]).

cnf(c_0_56,plain,
    ( r2_lattice3(X1,X2,X3)
    | r1_orders_2(X4,esk1_3(X1,X2,X3),k1_yellow_0(X4,X2))
    | ~ v5_orders_2(X4)
    | ~ r1_yellow_0(X4,X2)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39]),
    [final]).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_39]),
    [final]).

cnf(c_0_58,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | esk1_3(X1,X2,k1_yellow_0(X1,X3)) != k1_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39]),
    [final]).

cnf(c_0_59,plain,
    ( r1_orders_2(X1,X2,k1_yellow_0(X1,X3))
    | X2 != k1_yellow_0(X1,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_39]),
    [final]).

cnf(c_0_60,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X2))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39]),
    [final]).

cnf(c_0_61,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_39]),
    [final]).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_39]),
    [final]).

cnf(c_0_63,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r1_orders_2(X2,esk2_3(X2,X3,X1),esk2_3(X2,X3,X1))
    | v2_struct_0(X2)
    | ~ r1_yellow_0(X2,X3)
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_15]),
    [final]).

cnf(c_0_64,plain,
    ( r1_yellow_0(X1,X2)
    | r1_orders_2(X1,esk4_3(X1,X2,X3),esk4_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_17]),
    [final]).

cnf(c_0_65,plain,
    ( r2_lattice3(X1,X2,X3)
    | r1_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33]),
    [final]).

cnf(c_0_66,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X3))
    | esk1_3(X1,X2,k1_yellow_0(X1,X3)) != k1_yellow_0(X1,X3)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_45]),c_0_33]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk6_0))
    | k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk6_0)) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk5_0,esk6_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_46]),c_0_47]),c_0_48])]),c_0_49]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:03:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.032 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # No proof found!
% 0.19/0.38  # SZS status CounterSatisfiable
% 0.19/0.38  # SZS output start Saturation
% 0.19/0.38  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.19/0.38  fof(t15_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(r1_yellow_0(X1,X2)<=>?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow_0)).
% 0.19/0.38  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.19/0.38  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.19/0.38  fof(t34_waybel_0, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r1_yellow_0(X1,k5_waybel_0(X1,X2))&k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_waybel_0)).
% 0.19/0.38  fof(c_0_5, plain, ![X12, X13, X14, X15]:(((r2_lattice3(X12,X13,X14)|X14!=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_lattice3(X12,X13,X15)|r1_orders_2(X12,X14,X15))|X14!=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12)))&((m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))|~r2_lattice3(X12,X13,X14)|X14=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&((r2_lattice3(X12,X13,esk2_3(X12,X13,X14))|~r2_lattice3(X12,X13,X14)|X14=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))&(~r1_orders_2(X12,X14,esk2_3(X12,X13,X14))|~r2_lattice3(X12,X13,X14)|X14=k1_yellow_0(X12,X13)|~r1_yellow_0(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|~l1_orders_2(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.19/0.38  fof(c_0_6, plain, ![X17, X18, X20, X21, X22]:((((m1_subset_1(esk3_2(X17,X18),u1_struct_0(X17))|~r1_yellow_0(X17,X18)|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(r2_lattice3(X17,X18,esk3_2(X17,X18))|~r1_yellow_0(X17,X18)|(~v5_orders_2(X17)|~l1_orders_2(X17))))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_lattice3(X17,X18,X20)|r1_orders_2(X17,esk3_2(X17,X18),X20))|~r1_yellow_0(X17,X18)|(~v5_orders_2(X17)|~l1_orders_2(X17))))&((m1_subset_1(esk4_3(X17,X21,X22),u1_struct_0(X17))|(~m1_subset_1(X22,u1_struct_0(X17))|~r2_lattice3(X17,X21,X22))|r1_yellow_0(X17,X21)|(~v5_orders_2(X17)|~l1_orders_2(X17)))&((r2_lattice3(X17,X21,esk4_3(X17,X21,X22))|(~m1_subset_1(X22,u1_struct_0(X17))|~r2_lattice3(X17,X21,X22))|r1_yellow_0(X17,X21)|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(~r1_orders_2(X17,X22,esk4_3(X17,X21,X22))|(~m1_subset_1(X22,u1_struct_0(X17))|~r2_lattice3(X17,X21,X22))|r1_yellow_0(X17,X21)|(~v5_orders_2(X17)|~l1_orders_2(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).
% 0.19/0.38  fof(c_0_7, plain, ![X7, X8, X9, X10]:((~r2_lattice3(X7,X8,X9)|(~m1_subset_1(X10,u1_struct_0(X7))|(~r2_hidden(X10,X8)|r1_orders_2(X7,X10,X9)))|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&((m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))|r2_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&((r2_hidden(esk1_3(X7,X8,X9),X8)|r2_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&(~r1_orders_2(X7,esk1_3(X7,X8,X9),X9)|r2_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.19/0.38  cnf(c_0_8, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_9, plain, (r1_orders_2(X2,esk3_2(X2,X3),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~r1_yellow_0(X2,X3)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_10, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|~r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_11, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_12, plain, (r2_lattice3(X1,X2,esk3_2(X1,X2))|~r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_13, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.19/0.38  cnf(c_0_14, plain, (r2_lattice3(X1,X2,esk2_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_15, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_16, plain, (r2_lattice3(X1,X2,esk4_3(X1,X2,X3))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_17, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_18, plain, (esk3_2(X1,X2)=k1_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,esk2_3(X1,X3,esk3_2(X1,X2)))|~r2_lattice3(X1,X3,esk3_2(X1,X2))|~m1_subset_1(esk2_3(X1,X3,esk3_2(X1,X2)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), ['final']).
% 0.19/0.38  cnf(c_0_19, plain, (r2_lattice3(X1,X2,X3)|X3!=k1_yellow_0(X1,X2)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_20, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.19/0.38  cnf(c_0_21, plain, (r1_orders_2(X1,X2,esk3_2(X1,X3))|X2!=k1_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_10]), ['final']).
% 0.19/0.38  fof(c_0_22, plain, ![X5, X6]:(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|r1_orders_2(X5,X6,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.19/0.38  fof(c_0_23, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r1_yellow_0(X1,k5_waybel_0(X1,X2))&k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2)))), inference(assume_negation,[status(cth)],[t34_waybel_0])).
% 0.19/0.38  cnf(c_0_24, plain, (X1=k1_yellow_0(X2,X3)|r1_orders_2(X2,X4,esk2_3(X2,X3,X1))|~r1_yellow_0(X2,X3)|~r2_hidden(X4,X3)|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), ['final']).
% 0.19/0.38  cnf(c_0_25, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.19/0.38  cnf(c_0_26, plain, (r1_yellow_0(X1,X2)|r1_orders_2(X1,X3,esk4_3(X1,X2,X4))|~v5_orders_2(X1)|~r2_hidden(X3,X2)|~r2_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_16]), c_0_17]), ['final']).
% 0.19/0.38  cnf(c_0_27, plain, (X1=k1_yellow_0(X2,X3)|r1_orders_2(X2,X4,esk2_3(X2,X3,X1))|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_14]), c_0_15]), ['final']).
% 0.19/0.38  cnf(c_0_28, plain, (esk3_2(X1,X2)=k1_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_yellow_0(X1,X2)|~m1_subset_1(esk2_3(X1,X2,esk3_2(X1,X2)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_14]), c_0_10]), c_0_12])).
% 0.19/0.38  cnf(c_0_29, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X2)|~m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_19]), ['final']).
% 0.19/0.38  cnf(c_0_30, plain, (r1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk4_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_31, plain, (r1_orders_2(X1,X2,esk3_2(X1,X3))|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_12]), c_0_10]), ['final']).
% 0.19/0.38  cnf(c_0_32, plain, (r2_lattice3(X1,X2,esk3_2(X1,X3))|esk1_3(X1,X2,esk3_2(X1,X3))!=k1_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~m1_subset_1(esk1_3(X1,X2,esk3_2(X1,X3)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_10])).
% 0.19/0.38  cnf(c_0_33, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.19/0.38  cnf(c_0_34, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.19/0.38  fof(c_0_35, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(~r1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk6_0))|k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk6_0))!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.19/0.38  cnf(c_0_36, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X4,X3,X5)|r1_orders_2(X2,esk1_3(X4,X3,X5),esk2_3(X2,X3,X1))|~r1_yellow_0(X2,X3)|~r2_lattice3(X2,X3,X1)|~m1_subset_1(esk1_3(X4,X3,X5),u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X5,u1_struct_0(X4))|~l1_orders_2(X2)|~l1_orders_2(X4)), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_37, plain, (r1_yellow_0(X1,X2)|r2_lattice3(X3,X2,X4)|r1_orders_2(X1,esk1_3(X3,X2,X4),esk4_3(X1,X2,X5))|~v5_orders_2(X1)|~r2_lattice3(X1,X2,X5)|~m1_subset_1(esk1_3(X3,X2,X4),u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X3))|~l1_orders_2(X1)|~l1_orders_2(X3)), inference(spm,[status(thm)],[c_0_26, c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_38, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X4,esk2_3(X2,X3,X1))|esk1_3(X2,X4,esk2_3(X2,X3,X1))!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~r2_lattice3(X2,X3,X1)|~m1_subset_1(esk1_3(X2,X4,esk2_3(X2,X3,X1)),u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_27]), c_0_15])).
% 0.19/0.38  cnf(c_0_39, plain, (esk3_2(X1,X2)=k1_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_15]), c_0_10]), c_0_12]), ['final']).
% 0.19/0.38  cnf(c_0_40, plain, (r1_orders_2(X1,X2,k1_yellow_0(X1,X3))|~r1_yellow_0(X1,X3)|~r2_hidden(X2,X3)|~m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_13, c_0_29]), ['final']).
% 0.19/0.38  cnf(c_0_41, plain, (r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~r2_lattice3(X1,X3,esk4_3(X1,X2,esk3_2(X1,X3)))|~r2_lattice3(X1,X2,esk3_2(X1,X3))|~m1_subset_1(esk4_3(X1,X2,esk3_2(X1,X3)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_9]), c_0_10]), ['final']).
% 0.19/0.38  cnf(c_0_42, plain, (r2_lattice3(X1,X2,X3)|r1_orders_2(X4,esk1_3(X1,X2,X3),esk3_2(X4,X2))|~v5_orders_2(X4)|~r1_yellow_0(X4,X2)|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X4)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_31, c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_43, plain, (r2_lattice3(X1,X2,esk3_2(X1,X3))|esk1_3(X1,X2,esk3_2(X1,X3))!=k1_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_10]), ['final']).
% 0.19/0.38  cnf(c_0_44, plain, (r1_orders_2(X1,esk3_2(X1,X2),esk3_2(X1,X2))|v2_struct_0(X1)|~v5_orders_2(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_10]), ['final']).
% 0.19/0.38  cnf(c_0_45, plain, (r1_orders_2(X1,X2,k1_yellow_0(X1,X3))|X2!=k1_yellow_0(X1,X3)|~r1_yellow_0(X1,X3)|~m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_11, c_0_29]), ['final']).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_50, plain, (esk1_3(X1,X2,X3)=k1_yellow_0(X4,X2)|r2_lattice3(X1,X2,X3)|~r1_yellow_0(X4,X2)|~r2_lattice3(X4,X2,esk1_3(X1,X2,X3))|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X4)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_8, c_0_36]), ['final']).
% 0.19/0.38  cnf(c_0_51, plain, (r1_yellow_0(X1,X2)|r2_lattice3(X3,X2,X4)|~v5_orders_2(X1)|~r2_lattice3(X1,X2,esk1_3(X3,X2,X4))|~m1_subset_1(esk1_3(X3,X2,X4),u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X3))|~l1_orders_2(X1)|~l1_orders_2(X3)), inference(spm,[status(thm)],[c_0_30, c_0_37]), ['final']).
% 0.19/0.38  cnf(c_0_52, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X4,esk2_3(X2,X3,X1))|esk1_3(X2,X4,esk2_3(X2,X3,X1))!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_33]), c_0_15]), ['final']).
% 0.19/0.38  cnf(c_0_53, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,esk2_3(X1,X3,k1_yellow_0(X1,X2)))|~r2_lattice3(X1,X3,k1_yellow_0(X1,X2))|~m1_subset_1(esk2_3(X1,X3,k1_yellow_0(X1,X2)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_54, plain, (r2_lattice3(X1,X2,X3)|r1_orders_2(X4,esk1_3(X1,X2,X3),k1_yellow_0(X4,X2))|~r1_yellow_0(X4,X2)|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))|~m1_subset_1(k1_yellow_0(X4,X2),u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X4)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_40, c_0_25]), ['final']).
% 0.19/0.38  cnf(c_0_55, plain, (r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~r2_lattice3(X1,X3,esk4_3(X1,X2,k1_yellow_0(X1,X3)))|~r2_lattice3(X1,X2,k1_yellow_0(X1,X3))|~m1_subset_1(esk4_3(X1,X2,k1_yellow_0(X1,X3)),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_56, plain, (r2_lattice3(X1,X2,X3)|r1_orders_2(X4,esk1_3(X1,X2,X3),k1_yellow_0(X4,X2))|~v5_orders_2(X4)|~r1_yellow_0(X4,X2)|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X4)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_42, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_57, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~v5_orders_2(X1)|~r1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_9, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_58, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X3))|esk1_3(X1,X2,k1_yellow_0(X1,X3))!=k1_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_43, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_59, plain, (r1_orders_2(X1,X2,k1_yellow_0(X1,X3))|X2!=k1_yellow_0(X1,X3)|~v5_orders_2(X1)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_21, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_60, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X2))|v2_struct_0(X1)|~v5_orders_2(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_44, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_61, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~v5_orders_2(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_12, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_62, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~v5_orders_2(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_10, c_0_39]), ['final']).
% 0.19/0.38  cnf(c_0_63, plain, (X1=k1_yellow_0(X2,X3)|r1_orders_2(X2,esk2_3(X2,X3,X1),esk2_3(X2,X3,X1))|v2_struct_0(X2)|~r1_yellow_0(X2,X3)|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~v3_orders_2(X2)), inference(spm,[status(thm)],[c_0_34, c_0_15]), ['final']).
% 0.19/0.38  cnf(c_0_64, plain, (r1_yellow_0(X1,X2)|r1_orders_2(X1,esk4_3(X1,X2,X3),esk4_3(X1,X2,X3))|v2_struct_0(X1)|~v5_orders_2(X1)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_17]), ['final']).
% 0.19/0.38  cnf(c_0_65, plain, (r2_lattice3(X1,X2,X3)|r1_orders_2(X1,esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_34, c_0_33]), ['final']).
% 0.19/0.38  cnf(c_0_66, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X3))|esk1_3(X1,X2,k1_yellow_0(X1,X3))!=k1_yellow_0(X1,X3)|~r1_yellow_0(X1,X3)|~m1_subset_1(k1_yellow_0(X1,X3),u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_45]), c_0_33]), ['final']).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (~r1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk6_0))|k1_yellow_0(esk5_0,k5_waybel_0(esk5_0,esk6_0))!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (r1_orders_2(esk5_0,esk6_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_46]), c_0_47]), c_0_48])]), c_0_49]), ['final']).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.19/0.38  # SZS output end Saturation
% 0.19/0.38  # Proof object total steps             : 71
% 0.19/0.38  # Proof object clause steps            : 60
% 0.19/0.38  # Proof object formula steps           : 11
% 0.19/0.38  # Proof object conjectures             : 11
% 0.19/0.38  # Proof object clause conjectures      : 8
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 23
% 0.19/0.38  # Proof object initial formulas used   : 5
% 0.19/0.38  # Proof object generating inferences   : 37
% 0.19/0.38  # Proof object simplifying inferences  : 20
% 0.19/0.38  # Parsed axioms                        : 5
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 23
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 23
% 0.19/0.38  # Processed clauses                    : 94
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 11
% 0.19/0.38  # ...remaining for further processing  : 83
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 3
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 52
% 0.19/0.38  # ...of the previous two non-trivial   : 48
% 0.19/0.38  # Contextual simplify-reflections      : 16
% 0.19/0.38  # Paramodulations                      : 51
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 1
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 57
% 0.19/0.38  #    Positive orientable unit clauses  : 6
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 50
% 0.19/0.38  # Current number of unprocessed clauses: 0
% 0.19/0.38  # ...number of literals in the above   : 0
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 26
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1239
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 85
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 30
% 0.19/0.38  # Unit Clause-clause subsumption calls : 0
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4491
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.038 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.044 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
