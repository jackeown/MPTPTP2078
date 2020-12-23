%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t48_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:43 EDT 2019

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :   73 (1621 expanded)
%              Number of clauses        :   68 ( 545 expanded)
%              Number of leaves         :    2 ( 407 expanded)
%              Depth                    :   20
%              Number of atoms          :  515 (25729 expanded)
%              Number of equality atoms :   38 (1157 expanded)
%              Maximal formula depth    :   33 (   7 average)
%              Maximal clause size      :  107 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) )
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattice3(X1,X2,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r1_lattice3(X1,X2,X5)
                           => r1_orders_2(X1,X5,X4) ) ) )
                   => X4 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t48_yellow_0.p',d8_yellow_0)).

fof(t48_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) )
            & r2_yellow_0(X1,X2) )
         => r2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t48_yellow_0.p',t48_yellow_0)).

fof(c_0_2,plain,(
    ! [X12,X13,X15,X16,X18,X19,X22] :
      ( ( m1_subset_1(esk4_2(X12,X13),u1_struct_0(X12))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X13,esk4_2(X12,X13))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X13,X15)
        | r1_orders_2(X12,X15,esk4_2(X12,X13))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk5_3(X12,X13,X16),u1_struct_0(X12))
        | ~ r1_lattice3(X12,X13,X16)
        | X16 = esk4_2(X12,X13)
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X13,esk5_3(X12,X13,X16))
        | ~ r1_lattice3(X12,X13,X16)
        | X16 = esk4_2(X12,X13)
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,esk5_3(X12,X13,X16),X16)
        | ~ r1_lattice3(X12,X13,X16)
        | X16 = esk4_2(X12,X13)
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk7_3(X12,X18,X19),u1_struct_0(X12))
        | m1_subset_1(esk6_3(X12,X18,X19),u1_struct_0(X12))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X18,esk7_3(X12,X18,X19))
        | m1_subset_1(esk6_3(X12,X18,X19),u1_struct_0(X12))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X22)
        | r1_orders_2(X12,X22,esk7_3(X12,X18,X19))
        | m1_subset_1(esk6_3(X12,X18,X19),u1_struct_0(X12))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( esk7_3(X12,X18,X19) != X19
        | m1_subset_1(esk6_3(X12,X18,X19),u1_struct_0(X12))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk7_3(X12,X18,X19),u1_struct_0(X12))
        | r1_lattice3(X12,X18,esk6_3(X12,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X18,esk7_3(X12,X18,X19))
        | r1_lattice3(X12,X18,esk6_3(X12,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X22)
        | r1_orders_2(X12,X22,esk7_3(X12,X18,X19))
        | r1_lattice3(X12,X18,esk6_3(X12,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( esk7_3(X12,X18,X19) != X19
        | r1_lattice3(X12,X18,esk6_3(X12,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk7_3(X12,X18,X19),u1_struct_0(X12))
        | ~ r1_orders_2(X12,esk6_3(X12,X18,X19),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X18,esk7_3(X12,X18,X19))
        | ~ r1_orders_2(X12,esk6_3(X12,X18,X19),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X22)
        | r1_orders_2(X12,X22,esk7_3(X12,X18,X19))
        | ~ r1_orders_2(X12,esk6_3(X12,X18,X19),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( esk7_3(X12,X18,X19) != X19
        | ~ r1_orders_2(X12,esk6_3(X12,X18,X19),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_0])])])])])])).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( ( ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                  <=> r1_lattice3(X1,X3,X4) ) )
              & r2_yellow_0(X1,X2) )
           => r2_yellow_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t48_yellow_0])).

cnf(c_0_4,plain,
    ( X3 = esk4_2(X1,X2)
    | ~ r1_orders_2(X1,esk5_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_5,plain,
    ( r1_orders_2(X2,X1,esk7_3(X2,X3,X4))
    | r1_lattice3(X2,X3,esk6_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_6,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

fof(c_0_7,negated_conjecture,(
    ! [X9] :
      ( ~ v2_struct_0(esk1_0)
      & l1_orders_2(esk1_0)
      & ( ~ r1_lattice3(esk1_0,esk2_0,X9)
        | r1_lattice3(esk1_0,esk3_0,X9)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0)) )
      & ( ~ r1_lattice3(esk1_0,esk3_0,X9)
        | r1_lattice3(esk1_0,esk2_0,X9)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0)) )
      & r2_yellow_0(esk1_0,esk2_0)
      & ~ r2_yellow_0(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

cnf(c_0_8,plain,
    ( esk7_3(X1,X2,X3) = esk4_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X4)
    | ~ r1_lattice3(X1,X2,esk5_3(X1,X4,esk7_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk7_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk5_3(X1,X4,esk7_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_4,c_0_5]),c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,X1)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_14,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,X1) = esk4_2(esk1_0,X2)
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,X1))
    | ~ r2_yellow_0(esk1_0,X2)
    | ~ r1_lattice3(esk1_0,esk2_0,esk5_3(esk1_0,X2,esk7_3(esk1_0,esk3_0,X1)))
    | ~ r1_lattice3(esk1_0,X2,esk7_3(esk1_0,esk3_0,X1))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(esk5_3(esk1_0,X2,esk7_3(esk1_0,esk3_0,X1)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_15,plain,
    ( r1_lattice3(X1,X2,esk5_3(X1,X2,X3))
    | X3 = esk4_2(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_16,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,X1))
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk3_0,X1))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(esk7_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_10])]),c_0_11])).

cnf(c_0_18,plain,
    ( r1_orders_2(X2,X1,esk7_3(X2,X3,X4))
    | m1_subset_1(esk6_3(X2,X3,X4),u1_struct_0(X2))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_20,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,X1) = esk4_2(esk1_0,esk2_0)
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,X1))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(esk5_3(esk1_0,esk2_0,esk7_3(esk1_0,esk3_0,X1)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk7_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_10])]),c_0_17])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = esk4_2(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_22,plain,
    ( esk7_3(X1,X2,X3) = esk4_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X4)
    | ~ r1_lattice3(X1,X2,esk5_3(X1,X4,esk7_3(X1,X2,X3)))
    | ~ r1_lattice3(X1,X4,esk7_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(esk5_3(X1,X4,esk7_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_4,c_0_18]),c_0_19])).

cnf(c_0_23,plain,
    ( r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_24,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,X1) = esk4_2(esk1_0,esk2_0)
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,X1))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(esk7_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16]),c_0_10])]),c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,X1) = esk4_2(esk1_0,X2)
    | m1_subset_1(esk6_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ r2_yellow_0(esk1_0,X2)
    | ~ r1_lattice3(esk1_0,esk2_0,esk5_3(esk1_0,X2,esk7_3(esk1_0,esk3_0,X1)))
    | ~ r1_lattice3(esk1_0,X2,esk7_3(esk1_0,esk3_0,X1))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(esk5_3(esk1_0,X2,esk7_3(esk1_0,esk3_0,X1)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk3_0,X1))
    | m1_subset_1(esk6_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(esk7_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_23]),c_0_10])]),c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,X1) = esk4_2(esk1_0,esk2_0)
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,X1))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_6]),c_0_10])]),c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,X1) = esk4_2(esk1_0,esk2_0)
    | m1_subset_1(esk6_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(esk5_3(esk1_0,esk2_0,esk7_3(esk1_0,esk3_0,X1)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk7_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_16]),c_0_10])]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_2(esk1_0,esk2_0))
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,X2))
    | ~ r1_lattice3(esk1_0,esk3_0,X2)
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_27]),c_0_10])]),c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,X1) = esk4_2(esk1_0,esk2_0)
    | m1_subset_1(esk6_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(esk7_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_16]),c_0_10])]),c_0_26])).

cnf(c_0_31,plain,
    ( r1_orders_2(X2,X1,esk7_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,esk6_3(X2,X3,X4),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_32,plain,
    ( r1_orders_2(X2,X1,esk4_2(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_2(esk1_0,esk2_0))
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,X2))
    | ~ r1_lattice3(esk1_0,esk3_0,X2)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,X1) = esk4_2(esk1_0,esk2_0)
    | m1_subset_1(esk6_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_10])]),c_0_11])).

cnf(c_0_37,plain,
    ( r1_lattice3(X1,X2,esk6_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | esk7_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | esk7_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_39,plain,
    ( r1_orders_2(X1,X2,esk7_3(X1,X3,esk4_2(X1,X4)))
    | r2_yellow_0(X1,X3)
    | ~ r2_yellow_0(X1,X4)
    | ~ r1_lattice3(X1,X4,esk6_3(X1,X3,esk4_2(X1,X4)))
    | ~ r1_lattice3(X1,X3,esk4_2(X1,X4))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ m1_subset_1(esk6_3(X1,X3,esk4_2(X1,X4)),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_40,plain,
    ( r2_yellow_0(X1,X2)
    | m1_subset_1(esk7_3(X1,X2,esk4_2(X1,X3)),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,esk6_3(X1,X2,esk4_2(X1,X3)))
    | ~ r1_lattice3(X1,X2,esk4_2(X1,X3))
    | ~ m1_subset_1(esk6_3(X1,X2,esk4_2(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_33])).

cnf(c_0_41,plain,
    ( r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_2(esk1_0,esk2_0))
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X2)))
    | ~ r2_yellow_0(esk1_0,X2)
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,X2))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_10])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_2(esk1_0,esk2_0))
    | m1_subset_1(esk6_3(esk1_0,esk3_0,X2),u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk3_0,X2)
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_36]),c_0_10])]),c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,X1))
    | esk4_2(esk1_0,esk2_0) != X1
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_10])]),c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | esk4_2(esk1_0,esk2_0) != X1
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_10])]),c_0_11])).

cnf(c_0_46,plain,
    ( esk7_3(X1,X2,esk4_2(X1,X3)) = esk4_2(X1,X4)
    | r2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X4)
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X2,esk5_3(X1,X4,esk7_3(X1,X2,esk4_2(X1,X3))))
    | ~ r1_lattice3(X1,X4,esk7_3(X1,X2,esk4_2(X1,X3)))
    | ~ r1_lattice3(X1,X3,esk6_3(X1,X2,esk4_2(X1,X3)))
    | ~ r1_lattice3(X1,X2,esk4_2(X1,X3))
    | ~ m1_subset_1(esk5_3(X1,X4,esk7_3(X1,X2,esk4_2(X1,X3))),u1_struct_0(X1))
    | ~ m1_subset_1(esk6_3(X1,X2,esk4_2(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_4,c_0_39]),c_0_40])).

cnf(c_0_47,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,esk7_3(X1,X2,esk4_2(X1,X3)))
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,esk6_3(X1,X2,esk4_2(X1,X3)))
    | ~ r1_lattice3(X1,X2,esk4_2(X1,X3))
    | ~ m1_subset_1(esk6_3(X1,X2,esk4_2(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_2(esk1_0,esk2_0))
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X2)))
    | ~ r2_yellow_0(esk1_0,X2)
    | ~ r1_lattice3(esk1_0,esk2_0,esk4_2(esk1_0,X2))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(esk4_2(esk1_0,X2),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk3_0,X1),esk4_2(esk1_0,esk2_0))
    | m1_subset_1(esk6_3(esk1_0,esk3_0,X2),u1_struct_0(esk1_0))
    | esk4_2(esk1_0,esk2_0) != X1
    | ~ r1_lattice3(esk1_0,esk3_0,X2)
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)) = esk4_2(esk1_0,X2)
    | ~ r2_yellow_0(esk1_0,X2)
    | ~ r2_yellow_0(esk1_0,X1)
    | ~ r1_lattice3(esk1_0,esk2_0,esk5_3(esk1_0,X2,esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1))))
    | ~ r1_lattice3(esk1_0,X2,esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)))
    | ~ r1_lattice3(esk1_0,X1,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)))
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,X1))
    | ~ m1_subset_1(esk5_3(esk1_0,X2,esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1))),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_9]),c_0_10])]),c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)))
    | ~ r2_yellow_0(esk1_0,X1)
    | ~ r1_lattice3(esk1_0,X1,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)))
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,X1))
    | ~ m1_subset_1(esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_47]),c_0_10])]),c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_2(esk1_0,esk2_0))
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X2)))
    | ~ r2_yellow_0(esk1_0,X2)
    | ~ r1_lattice3(esk1_0,esk2_0,esk4_2(esk1_0,X2))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_10])])).

cnf(c_0_53,plain,
    ( r1_lattice3(X1,X2,esk4_2(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk3_0,X1),esk4_2(esk1_0,esk2_0))
    | m1_subset_1(esk6_3(esk1_0,esk3_0,X2),u1_struct_0(esk1_0))
    | esk4_2(esk1_0,esk2_0) != X1
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ r1_lattice3(esk1_0,esk2_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_9])).

cnf(c_0_55,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)) = esk4_2(esk1_0,esk2_0)
    | ~ r2_yellow_0(esk1_0,X1)
    | ~ r1_lattice3(esk1_0,X1,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)))
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,X1))
    | ~ m1_subset_1(esk5_3(esk1_0,esk2_0,esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1))),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_15]),c_0_16]),c_0_10])]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_2(esk1_0,esk2_0))
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0)))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_16]),c_0_10])])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk6_3(esk1_0,esk3_0,X1))
    | esk4_2(esk1_0,esk2_0) != X1
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_44]),c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk3_0,X1),esk4_2(esk1_0,esk2_0))
    | m1_subset_1(esk6_3(esk1_0,esk3_0,X2),u1_struct_0(esk1_0))
    | esk4_2(esk1_0,esk2_0) != X1
    | ~ r1_lattice3(esk1_0,esk2_0,X2)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_9])).

cnf(c_0_59,plain,
    ( r2_yellow_0(X1,X2)
    | esk7_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_60,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)) = esk4_2(esk1_0,esk2_0)
    | ~ r2_yellow_0(esk1_0,X1)
    | ~ r1_lattice3(esk1_0,X1,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)))
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,X1))
    | ~ m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_21]),c_0_16]),c_0_10])]),c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk3_0,X1),esk4_2(esk1_0,esk2_0))
    | r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0)))
    | esk4_2(esk1_0,esk2_0) != X1
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_45]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk3_0,X1),esk4_2(esk1_0,esk2_0))
    | m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | esk4_2(esk1_0,esk2_0) != X1
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(esk4_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_53]),c_0_16]),c_0_10])])).

cnf(c_0_63,plain,
    ( r2_yellow_0(X1,X2)
    | esk7_3(X1,X2,esk4_2(X1,X3)) != esk4_2(X1,X3)
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,esk6_3(X1,X2,esk4_2(X1,X3)))
    | ~ r1_lattice3(X1,X2,esk4_2(X1,X3))
    | ~ m1_subset_1(esk6_3(X1,X2,esk4_2(X1,X3)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_32]),c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( esk7_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)) = esk4_2(esk1_0,esk2_0)
    | ~ r2_yellow_0(esk1_0,X1)
    | ~ r1_lattice3(esk1_0,X1,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)))
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,X1))
    | ~ m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_40]),c_0_10])]),c_0_11])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0)))
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0))
    | ~ m1_subset_1(esk4_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_61]),c_0_10])]),c_0_11]),c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0))
    | ~ m1_subset_1(esk4_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_62]),c_0_10])]),c_0_11]),c_0_12]),c_0_36])).

cnf(c_0_67,negated_conjecture,
    ( esk4_2(esk1_0,esk2_0) != esk4_2(esk1_0,X1)
    | ~ r2_yellow_0(esk1_0,X1)
    | ~ r1_lattice3(esk1_0,X1,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)))
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,X1))
    | ~ m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,X1)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_10])]),c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk6_3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0)))
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0))
    | ~ m1_subset_1(esk4_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_65]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,esk3_0,esk4_2(esk1_0,esk2_0))
    | ~ m1_subset_1(esk4_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_16])]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,esk2_0,esk4_2(esk1_0,esk2_0))
    | ~ m1_subset_1(esk4_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_9])).

cnf(c_0_71,negated_conjecture,
    ( ~ m1_subset_1(esk4_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_53]),c_0_16]),c_0_10])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_33]),c_0_16]),c_0_10])]),
    [proof]).
%------------------------------------------------------------------------------
