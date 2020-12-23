%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t16_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:37 EDT 2019

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  171 (5921917134 expanded)
%              Number of clauses        :  164 (1993691281 expanded)
%              Number of leaves         :    3 (1440223092 expanded)
%              Depth                    :   47
%              Number of atoms          :  671 (91284212951 expanded)
%              Number of equality atoms :   64 (2746969474 expanded)
%              Maximal formula depth    :   33 (   4 average)
%              Maximal clause size      :  107 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_yellow_0,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t16_yellow_0.p',t16_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t16_yellow_0.p',d8_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t16_yellow_0.p',t25_orders_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( r2_yellow_0(X1,X2)
          <=> ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_yellow_0])).

fof(c_0_4,plain,(
    ! [X12,X13,X15,X16,X18,X19,X22] :
      ( ( m1_subset_1(esk5_2(X12,X13),u1_struct_0(X12))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X13,esk5_2(X12,X13))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X13,X15)
        | r1_orders_2(X12,X15,esk5_2(X12,X13))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk6_3(X12,X13,X16),u1_struct_0(X12))
        | ~ r1_lattice3(X12,X13,X16)
        | X16 = esk5_2(X12,X13)
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X13,esk6_3(X12,X13,X16))
        | ~ r1_lattice3(X12,X13,X16)
        | X16 = esk5_2(X12,X13)
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,esk6_3(X12,X13,X16),X16)
        | ~ r1_lattice3(X12,X13,X16)
        | X16 = esk5_2(X12,X13)
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | ~ r2_yellow_0(X12,X13)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk8_3(X12,X18,X19),u1_struct_0(X12))
        | m1_subset_1(esk7_3(X12,X18,X19),u1_struct_0(X12))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X18,esk8_3(X12,X18,X19))
        | m1_subset_1(esk7_3(X12,X18,X19),u1_struct_0(X12))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X22)
        | r1_orders_2(X12,X22,esk8_3(X12,X18,X19))
        | m1_subset_1(esk7_3(X12,X18,X19),u1_struct_0(X12))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( esk8_3(X12,X18,X19) != X19
        | m1_subset_1(esk7_3(X12,X18,X19),u1_struct_0(X12))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk8_3(X12,X18,X19),u1_struct_0(X12))
        | r1_lattice3(X12,X18,esk7_3(X12,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X18,esk8_3(X12,X18,X19))
        | r1_lattice3(X12,X18,esk7_3(X12,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X22)
        | r1_orders_2(X12,X22,esk8_3(X12,X18,X19))
        | r1_lattice3(X12,X18,esk7_3(X12,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( esk8_3(X12,X18,X19) != X19
        | r1_lattice3(X12,X18,esk7_3(X12,X18,X19))
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk8_3(X12,X18,X19),u1_struct_0(X12))
        | ~ r1_orders_2(X12,esk7_3(X12,X18,X19),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X18,esk8_3(X12,X18,X19))
        | ~ r1_orders_2(X12,esk7_3(X12,X18,X19),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X22)
        | r1_orders_2(X12,X22,esk8_3(X12,X18,X19))
        | ~ r1_orders_2(X12,esk7_3(X12,X18,X19),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) )
      & ( esk8_3(X12,X18,X19) != X19
        | ~ r1_orders_2(X12,esk7_3(X12,X18,X19),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r1_lattice3(X12,X18,X19)
        | r2_yellow_0(X12,X18)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_0])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X8,X11] :
      ( v5_orders_2(esk1_0)
      & l1_orders_2(esk1_0)
      & ( m1_subset_1(esk3_1(X8),u1_struct_0(esk1_0))
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk2_0,X8)
        | ~ r2_yellow_0(esk1_0,esk2_0) )
      & ( r1_lattice3(esk1_0,esk2_0,esk3_1(X8))
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk2_0,X8)
        | ~ r2_yellow_0(esk1_0,esk2_0) )
      & ( ~ r1_orders_2(esk1_0,esk3_1(X8),X8)
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk2_0,X8)
        | ~ r2_yellow_0(esk1_0,esk2_0) )
      & ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | r2_yellow_0(esk1_0,esk2_0) )
      & ( r1_lattice3(esk1_0,esk2_0,esk4_0)
        | r2_yellow_0(esk1_0,esk2_0) )
      & ( ~ m1_subset_1(X11,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk2_0,X11)
        | r1_orders_2(esk1_0,X11,esk4_0)
        | r2_yellow_0(esk1_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

cnf(c_0_6,plain,
    ( r1_lattice3(X1,X2,esk5_2(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk4_0)
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_1(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_13,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk4_0)
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_7]),c_0_8])])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_1(X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_10]),c_0_8])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_8])])).

cnf(c_0_18,plain,
    ( r1_orders_2(X2,X1,esk5_2(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0)))
    | r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_7]),c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk4_0)
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_12]),c_0_7]),c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk4_0)
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_12]),c_0_7]),c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0)))
    | m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_16]),c_0_10]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_16]),c_0_10]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_10]),c_0_17])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_26,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_8])]),c_0_7]),c_0_20]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_22]),c_0_8])]),c_0_10]),c_0_23]),c_0_24])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_13]),c_0_8])]),c_0_27])])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_32,plain,
    ( r1_orders_2(X2,X1,esk8_3(X2,X3,X4))
    | r1_lattice3(X2,X3,esk7_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_33,plain,
    ( r1_lattice3(X1,X2,esk8_3(X1,X2,X3))
    | r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_29]),c_0_8])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_30]),c_0_8])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk7_3(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_38,plain,
    ( r1_orders_2(X2,X1,esk8_3(X2,X3,X4))
    | m1_subset_1(esk7_3(X2,X3,X4),u1_struct_0(X2))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_39,plain,
    ( r1_lattice3(X1,X2,esk8_3(X1,X2,X3))
    | m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_40,plain,(
    ! [X28,X29,X30] :
      ( ~ v5_orders_2(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ r1_orders_2(X28,X29,X30)
      | ~ r1_orders_2(X28,X30,X29)
      | X29 = X30 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_47,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_27])])).

cnf(c_0_49,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_42]),c_0_8])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_43]),c_0_8])])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_26]),c_0_27])])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_45]),c_0_8])])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_29]),c_0_8])])).

cnf(c_0_55,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_46]),c_0_8])])).

cnf(c_0_56,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_27]),c_0_8]),c_0_49])]),c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_50]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_52]),c_0_27]),c_0_8]),c_0_49])]),c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_53]),c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_54]),c_0_29]),c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_55]),c_0_46]),c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( r1_orders_2(X2,X1,esk8_3(X2,X3,X4))
    | r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,esk7_3(X2,X3,X4),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_60]),c_0_61]),c_0_37])).

cnf(c_0_66,plain,
    ( r1_lattice3(X1,X2,esk8_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_67,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_62]),c_0_8])])).

cnf(c_0_68,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_63]),c_0_8])])).

cnf(c_0_69,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk8_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk7_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_42]),c_0_8])])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_65]),c_0_8])])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk7_3(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_73,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_orders_2(esk1_0,esk7_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_67]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk7_3(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_26]),c_0_27])])).

cnf(c_0_75,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_45]),c_0_8])])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_70]),c_0_42]),c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_71]),c_0_65]),c_0_51])).

cnf(c_0_78,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_orders_2(esk1_0,esk4_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_75]),c_0_45]),c_0_53])).

cnf(c_0_81,negated_conjecture,
    ( r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_76]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_78]),c_0_8])])).

cnf(c_0_83,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_79]),c_0_27]),c_0_8]),c_0_49])]),c_0_51])).

cnf(c_0_84,negated_conjecture,
    ( r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_80]),c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0)))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_54]),c_0_29]),c_0_35])).

cnf(c_0_86,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_54]),c_0_29]),c_0_35])).

cnf(c_0_87,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0)))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_55]),c_0_46]),c_0_36])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_55]),c_0_46]),c_0_36])).

cnf(c_0_89,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_82]),c_0_51]),c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_85]),c_0_8])]),c_0_29]),c_0_77]),c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_87]),c_0_8])]),c_0_46]),c_0_77]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_89]),c_0_8])])).

cnf(c_0_95,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_90]),c_0_8])])).

cnf(c_0_96,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_91]),c_0_8])])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_92]),c_0_93]),c_0_37])).

cnf(c_0_98,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_94]),c_0_89]),c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_96]),c_0_91]),c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_97]),c_0_8])])).

cnf(c_0_101,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_orders_2(esk1_0,esk7_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_98]),c_0_99])).

cnf(c_0_102,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_70]),c_0_42]),c_0_50])).

cnf(c_0_103,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_70]),c_0_42]),c_0_50])).

cnf(c_0_104,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0)))
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_100]),c_0_97]),c_0_51])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_100]),c_0_97]),c_0_51])).

cnf(c_0_106,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0)))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_75]),c_0_45]),c_0_53])).

cnf(c_0_108,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_75]),c_0_45]),c_0_53])).

cnf(c_0_109,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_102]),c_0_8])]),c_0_42]),c_0_76]),c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_104]),c_0_8])]),c_0_97]),c_0_77]),c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_106]),c_0_8])])).

cnf(c_0_112,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_orders_2(esk1_0,esk4_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_101])).

cnf(c_0_113,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_107]),c_0_8])]),c_0_45]),c_0_80]),c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_109]),c_0_110])])).

cnf(c_0_115,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_111]),c_0_106]),c_0_95])).

cnf(c_0_116,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_112]),c_0_27]),c_0_8]),c_0_49])]),c_0_77])).

cnf(c_0_117,negated_conjecture,
    ( r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_113]),c_0_110])])).

cnf(c_0_118,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_115]),c_0_77]),c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_118]),c_0_8])])).

cnf(c_0_122,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_119]),c_0_8])])).

cnf(c_0_123,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_120]),c_0_8])])).

cnf(c_0_124,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_121]),c_0_118]),c_0_95])).

cnf(c_0_125,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_122]),c_0_119]),c_0_95])).

cnf(c_0_126,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_121]),c_0_118]),c_0_95])).

cnf(c_0_127,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0)))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_123]),c_0_120]),c_0_95])).

cnf(c_0_128,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_123]),c_0_120]),c_0_95])).

cnf(c_0_129,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_124]),c_0_8])]),c_0_118]),c_0_125]),c_0_126])).

cnf(c_0_130,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_127]),c_0_8])]),c_0_120]),c_0_125]),c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_orders_2(esk1_0,esk7_3(esk1_0,esk2_0,esk4_0),esk4_0)
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_129]),c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_132]),c_0_8])])).

cnf(c_0_134,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_133]),c_0_132]),c_0_95])).

cnf(c_0_135,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_133]),c_0_132]),c_0_95])).

cnf(c_0_136,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_orders_2(esk1_0,esk4_0,esk8_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_131])).

cnf(c_0_137,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_134]),c_0_8])]),c_0_132]),c_0_125]),c_0_135])).

cnf(c_0_138,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk8_3(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_136]),c_0_27]),c_0_110]),c_0_8]),c_0_49])])).

cnf(c_0_139,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_137]),c_0_110])]),c_0_138])).

cnf(c_0_140,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_139]),c_0_8])])).

cnf(c_0_141,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_140]),c_0_139]),c_0_95])).

cnf(c_0_142,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_140]),c_0_139]),c_0_95])).

cnf(c_0_143,plain,
    ( r1_lattice3(X1,X2,esk7_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | esk8_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_144,negated_conjecture,
    ( esk8_3(esk1_0,esk2_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_141]),c_0_8])]),c_0_139]),c_0_125]),c_0_142])).

cnf(c_0_145,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | esk8_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_146,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_147,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_144]),c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_148,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_146]),c_0_8])])).

cnf(c_0_149,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_146]),c_0_8])])).

cnf(c_0_150,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_147]),c_0_8])])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_147]),c_0_8])])).

cnf(c_0_152,plain,
    ( r2_yellow_0(X1,X2)
    | esk8_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_153,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_148]),c_0_146]),c_0_149])).

cnf(c_0_154,negated_conjecture,
    ( m1_subset_1(esk7_3(esk1_0,esk2_0,esk4_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_150]),c_0_147]),c_0_151])).

cnf(c_0_155,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk7_3(esk1_0,esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_144]),c_0_26]),c_0_27]),c_0_8])])).

cnf(c_0_156,negated_conjecture,
    ( m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_153]),c_0_154]),c_0_155])).

cnf(c_0_157,negated_conjecture,
    ( m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_149]),c_0_151]),c_0_155])).

cnf(c_0_158,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0))
    | m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_156]),c_0_8])])).

cnf(c_0_159,negated_conjecture,
    ( m1_subset_1(esk5_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_157]),c_0_8])])).

cnf(c_0_160,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_148]),c_0_146]),c_0_149])).

cnf(c_0_161,negated_conjecture,
    ( m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_158]),c_0_159])]),c_0_156])).

cnf(c_0_162,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0))
    | ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_148]),c_0_146]),c_0_149])).

cnf(c_0_163,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk7_3(esk1_0,esk2_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_160]),c_0_8])]),c_0_161])]),c_0_146]),c_0_162])).

cnf(c_0_164,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_163]),c_0_147]),c_0_155])).

cnf(c_0_165,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_1(X1))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_164])])).

cnf(c_0_166,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk5_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_164]),c_0_8])])).

cnf(c_0_167,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_1(X1),X1)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_164])])).

cnf(c_0_168,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_1(esk5_2(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_159])])).

cnf(c_0_169,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_166]),c_0_159])])).

cnf(c_0_170,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_168]),c_0_161]),c_0_164]),c_0_8])]),c_0_169]),
    [proof]).
%------------------------------------------------------------------------------
