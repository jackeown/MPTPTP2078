%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1529+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:20 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 994 expanded)
%              Number of clauses        :   40 ( 402 expanded)
%              Number of leaves         :    4 ( 231 expanded)
%              Depth                    :   18
%              Number of atoms          :  292 (14875 expanded)
%              Number of equality atoms :   25 ( 605 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   67 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t7_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X2,X3) )
                & ( r1_orders_2(X1,X2,X3)
                 => r1_lattice3(X1,k1_tarski(X3),X2) )
                & ( r2_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X3,X2) )
                & ( r1_orders_2(X1,X3,X2)
                 => r2_lattice3(X1,k1_tarski(X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

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

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_5,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ r1_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X13)
        | r1_orders_2(X12,X14,X15)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))
        | r1_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | r1_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,X14,esk2_3(X12,X13,X14))
        | r1_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ( r1_lattice3(X1,k1_tarski(X3),X2)
                   => r1_orders_2(X1,X2,X3) )
                  & ( r1_orders_2(X1,X2,X3)
                   => r1_lattice3(X1,k1_tarski(X3),X2) )
                  & ( r2_lattice3(X1,k1_tarski(X3),X2)
                   => r1_orders_2(X1,X3,X2) )
                  & ( r1_orders_2(X1,X3,X2)
                   => r2_lattice3(X1,k1_tarski(X3),X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_0])).

cnf(c_0_7,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_hidden(X20,X18)
        | r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X17))
        | r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk3_3(X17,X18,X19),X18)
        | r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,esk3_3(X17,X18,X19),X19)
        | r2_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_10,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) )
    & ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r1_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) )
    & ( r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
      | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_11,plain,
    ( esk2_3(X1,X2,X3) = X4
    | r1_lattice3(X1,X2,X3)
    | X2 != k1_tarski(X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( esk2_3(X1,k1_tarski(X2),X3) = X2
    | r1_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k1_tarski(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_21,plain,
    ( r1_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,X1,esk5_0)
    | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k1_tarski(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_18]),c_0_14]),c_0_15])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k1_tarski(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14]),c_0_15])])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,X1,esk5_0)
    | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | k1_tarski(esk6_0) != k1_tarski(X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,X1,esk5_0)
    | k1_tarski(esk6_0) != k1_tarski(X1)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k1_tarski(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_14]),c_0_15])]),c_0_30])).

cnf(c_0_32,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,X1)
    | k1_tarski(esk6_0) != k1_tarski(X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_34,plain,
    ( esk3_3(X1,X2,X3) = X4
    | r2_lattice3(X1,X2,X3)
    | X2 != k1_tarski(X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_26])]),c_0_30])).

cnf(c_0_37,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,plain,
    ( esk3_3(X1,k1_tarski(X2),X3) = X2
    | r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_40,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_36]),c_0_14]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0)
    | ~ r2_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_36])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_14]),c_0_15])])).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk4_0,k1_tarski(esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_36]),c_0_14]),c_0_15])]),c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k1_tarski(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_45]),c_0_14]),c_0_15])])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | k1_tarski(esk6_0) != k1_tarski(X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_26])]),c_0_44]),
    [proof]).

%------------------------------------------------------------------------------
