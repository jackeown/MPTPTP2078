%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1537+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   54 (1263 expanded)
%              Number of clauses        :   47 ( 450 expanded)
%              Number of leaves         :    3 ( 304 expanded)
%              Depth                    :   16
%              Number of atoms          :  375 (20646 expanded)
%              Number of equality atoms :   26 ( 699 expanded)
%              Maximal formula depth    :   33 (   6 average)
%              Maximal clause size      :  107 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_yellow_0,conjecture,(
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

fof(d7_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) )
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r2_lattice3(X1,X2,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r2_lattice3(X1,X2,X5)
                           => r1_orders_2(X1,X4,X5) ) ) )
                   => X4 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_yellow_0)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t15_yellow_0])).

fof(c_0_4,negated_conjecture,(
    ! [X22,X25] :
      ( v5_orders_2(esk5_0)
      & l1_orders_2(esk5_0)
      & ( m1_subset_1(esk7_1(X22),u1_struct_0(esk5_0))
        | ~ m1_subset_1(X22,u1_struct_0(esk5_0))
        | ~ r2_lattice3(esk5_0,esk6_0,X22)
        | ~ r1_yellow_0(esk5_0,esk6_0) )
      & ( r2_lattice3(esk5_0,esk6_0,esk7_1(X22))
        | ~ m1_subset_1(X22,u1_struct_0(esk5_0))
        | ~ r2_lattice3(esk5_0,esk6_0,X22)
        | ~ r1_yellow_0(esk5_0,esk6_0) )
      & ( ~ r1_orders_2(esk5_0,X22,esk7_1(X22))
        | ~ m1_subset_1(X22,u1_struct_0(esk5_0))
        | ~ r2_lattice3(esk5_0,esk6_0,X22)
        | ~ r1_yellow_0(esk5_0,esk6_0) )
      & ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
        | r1_yellow_0(esk5_0,esk6_0) )
      & ( r2_lattice3(esk5_0,esk6_0,esk8_0)
        | r1_yellow_0(esk5_0,esk6_0) )
      & ( ~ m1_subset_1(X25,u1_struct_0(esk5_0))
        | ~ r2_lattice3(esk5_0,esk6_0,X25)
        | r1_orders_2(esk5_0,esk8_0,X25)
        | r1_yellow_0(esk5_0,esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

fof(c_0_5,plain,(
    ! [X6,X7,X9,X10,X12,X13,X16] :
      ( ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X7,esk1_2(X6,X7))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X7,X9)
        | r1_orders_2(X6,esk1_2(X6,X7),X9)
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X10),u1_struct_0(X6))
        | ~ r2_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X7,esk2_3(X6,X7,X10))
        | ~ r2_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( ~ r1_orders_2(X6,X10,esk2_3(X6,X7,X10))
        | ~ r2_lattice3(X6,X7,X10)
        | X10 = esk1_2(X6,X7)
        | ~ m1_subset_1(X10,u1_struct_0(X6))
        | ~ r1_yellow_0(X6,X7)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X16)
        | r1_orders_2(X6,esk4_3(X6,X12,X13),X16)
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | m1_subset_1(esk3_3(X6,X12,X13),u1_struct_0(X6))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X16)
        | r1_orders_2(X6,esk4_3(X6,X12,X13),X16)
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | r2_lattice3(X6,X12,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk4_3(X6,X12,X13),u1_struct_0(X6))
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( r2_lattice3(X6,X12,esk4_3(X6,X12,X13))
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X16)
        | r1_orders_2(X6,esk4_3(X6,X12,X13),X16)
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) )
      & ( esk4_3(X6,X12,X13) != X13
        | ~ r1_orders_2(X6,X13,esk3_3(X6,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r2_lattice3(X6,X12,X13)
        | r1_yellow_0(X6,X12)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_yellow_0])])])])])])).

cnf(c_0_6,negated_conjecture,
    ( ~ r1_orders_2(esk5_0,X1,esk7_1(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ r1_yellow_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk7_1(X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ r1_yellow_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( ~ r2_lattice3(esk5_0,X1,esk7_1(esk1_2(esk5_0,X1)))
    | ~ r2_lattice3(esk5_0,esk6_0,esk1_2(esk5_0,X1))
    | ~ m1_subset_1(esk1_2(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ r1_yellow_0(esk5_0,esk6_0)
    | ~ r1_yellow_0(esk5_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])]),c_0_9])).

cnf(c_0_11,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk7_1(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ r1_yellow_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_lattice3(esk5_0,esk6_0,esk1_2(esk5_0,esk6_0))
    | ~ m1_subset_1(esk1_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ r1_yellow_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( ~ m1_subset_1(esk1_2(esk5_0,esk6_0),u1_struct_0(esk5_0))
    | ~ r1_yellow_0(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_8])])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_16,plain,(
    ! [X17,X18,X19] :
      ( ~ v5_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | ~ r1_orders_2(X17,X18,X19)
      | ~ r1_orders_2(X17,X19,X18)
      | X18 = X19 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    | r1_yellow_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_yellow_0(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_8])])).

cnf(c_0_19,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk5_0,esk8_0,X1)
    | r1_yellow_0(esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( X1 = esk8_0
    | ~ r1_orders_2(esk5_0,X1,esk8_0)
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_8])]),c_0_22])]),c_0_18])).

cnf(c_0_24,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,esk3_3(X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk8_0)
    | r1_yellow_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_26,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | m1_subset_1(esk3_3(X2,X3,X4),u1_struct_0(X2))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( esk4_3(esk5_0,X1,X2) = esk8_0
    | r1_yellow_0(esk5_0,X1)
    | ~ r1_orders_2(esk5_0,X2,esk3_3(esk5_0,X1,X2))
    | ~ r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,X1,X2))
    | ~ r2_lattice3(esk5_0,X1,esk8_0)
    | ~ r2_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_22]),c_0_8])])).

cnf(c_0_28,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( esk4_3(esk5_0,X1,X2) = esk8_0
    | m1_subset_1(esk3_3(esk5_0,X1,X2),u1_struct_0(esk5_0))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,X1,X2))
    | ~ r2_lattice3(esk5_0,X1,esk8_0)
    | ~ r2_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_26]),c_0_22]),c_0_8])])).

cnf(c_0_31,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_32,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | r2_lattice3(X2,X3,esk3_3(X2,X3,X4))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_33,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,X1) = esk8_0
    | ~ r1_orders_2(esk5_0,X1,esk3_3(esk5_0,esk6_0,X1))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(esk4_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_8])]),c_0_18])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_35,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,X1) = esk8_0
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(esk4_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_29]),c_0_8])]),c_0_18])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_37,negated_conjecture,
    ( esk4_3(esk5_0,X1,X2) = esk8_0
    | r2_lattice3(esk5_0,X1,esk3_3(esk5_0,X1,X2))
    | r1_yellow_0(esk5_0,X1)
    | ~ r2_lattice3(esk5_0,esk6_0,esk4_3(esk5_0,X1,X2))
    | ~ r2_lattice3(esk5_0,X1,esk8_0)
    | ~ r2_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_32]),c_0_22]),c_0_8])])).

cnf(c_0_38,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_39,plain,
    ( r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_40,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,X1) = esk8_0
    | ~ r1_orders_2(esk5_0,X1,esk3_3(esk5_0,esk6_0,X1))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_8])]),c_0_18])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_42,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,X1) = esk8_0
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_8])]),c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,X1) = esk8_0
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk6_0,X1))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(esk4_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_29]),c_0_8])]),c_0_18])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_45,negated_conjecture,
    ( esk8_0 != X1
    | ~ r1_orders_2(esk5_0,X1,esk3_3(esk5_0,esk6_0,X1))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_8])]),c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0))
    | esk8_0 != X1
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_8])]),c_0_18])).

cnf(c_0_47,plain,
    ( r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_48,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,X1) = esk8_0
    | r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk6_0,X1))
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_8])]),c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk6_0,esk8_0))
    | ~ m1_subset_1(esk3_3(esk5_0,esk6_0,esk8_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_20]),c_0_29]),c_0_22])]),c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,esk6_0,esk8_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_29]),c_0_22])])).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk6_0,X1))
    | esk8_0 != X1
    | ~ r2_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_8])]),c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_lattice3(esk5_0,esk6_0,esk3_3(esk5_0,esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_29]),c_0_22])]),c_0_52]),
    [proof]).

%------------------------------------------------------------------------------
