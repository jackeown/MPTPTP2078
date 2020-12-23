%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t10_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:36 EDT 2019

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   69 (1383 expanded)
%              Number of clauses        :   60 ( 521 expanded)
%              Number of leaves         :    4 ( 322 expanded)
%              Depth                    :   26
%              Number of atoms          :  283 (11699 expanded)
%              Number of equality atoms :    8 ( 104 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3,X4] :
          ( m1_subset_1(X4,u1_struct_0(X1))
         => ( ( ( r1_lattice3(X1,X2,X4)
                & r1_lattice3(X1,X3,X4) )
             => r1_lattice3(X1,k2_xboole_0(X2,X3),X4) )
            & ( ( r2_lattice3(X1,X2,X4)
                & r2_lattice3(X1,X3,X4) )
             => r2_lattice3(X1,k2_xboole_0(X2,X3),X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t10_yellow_0.p',t10_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t10_yellow_0.p',d9_lattice3)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t10_yellow_0.p',d3_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t10_yellow_0.p',d8_lattice3)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2,X3,X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ( ( ( r1_lattice3(X1,X2,X4)
                  & r1_lattice3(X1,X3,X4) )
               => r1_lattice3(X1,k2_xboole_0(X2,X3),X4) )
              & ( ( r2_lattice3(X1,X2,X4)
                  & r2_lattice3(X1,X3,X4) )
               => r2_lattice3(X1,k2_xboole_0(X2,X3),X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_yellow_0])).

fof(c_0_5,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r2_hidden(X30,X28)
        | r1_orders_2(X27,X30,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk7_3(X27,X28,X29),u1_struct_0(X27))
        | r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( r2_hidden(esk7_3(X27,X28,X29),X28)
        | r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,esk7_3(X27,X28,X29),X29)
        | r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_6,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & ( r2_lattice3(esk1_0,esk2_0,esk4_0)
      | r1_lattice3(esk1_0,esk2_0,esk4_0) )
    & ( r2_lattice3(esk1_0,esk3_0,esk4_0)
      | r1_lattice3(esk1_0,esk2_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0)
      | r1_lattice3(esk1_0,esk2_0,esk4_0) )
    & ( r2_lattice3(esk1_0,esk2_0,esk4_0)
      | r1_lattice3(esk1_0,esk3_0,esk4_0) )
    & ( r2_lattice3(esk1_0,esk3_0,esk4_0)
      | r1_lattice3(esk1_0,esk3_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0)
      | r1_lattice3(esk1_0,esk3_0,esk4_0) )
    & ( r2_lattice3(esk1_0,esk2_0,esk4_0)
      | ~ r1_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) )
    & ( r2_lattice3(esk1_0,esk3_0,esk4_0)
      | ~ r1_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) )
    & ( ~ r2_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0)
      | ~ r1_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk5_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk5_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk5_3(X18,X19,X20),X20)
        | r2_hidden(esk5_3(X18,X19,X20),X18)
        | r2_hidden(esk5_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk4_0)
    | m1_subset_1(esk7_3(esk1_0,X1,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,X1,esk4_0),X1)
    | r2_lattice3(esk1_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_9]),c_0_10])])).

cnf(c_0_17,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,X1,esk4_0),X2)
    | r2_lattice3(esk1_0,X1,esk4_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,esk4_0),X3)
    | ~ r2_lattice3(esk1_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_10])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,k2_xboole_0(X1,X2),esk4_0),X1)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(X1,X2),esk4_0),X2)
    | r2_lattice3(esk1_0,k2_xboole_0(X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(X1,X2),esk4_0),X3)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(X1,X2),esk4_0),X2)
    | r2_lattice3(esk1_0,k2_xboole_0(X1,X2),esk4_0)
    | ~ r2_lattice3(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(X1,X2),esk4_0),esk4_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(X1,X2),esk4_0),X2)
    | r2_lattice3(esk1_0,k2_xboole_0(X1,X2),esk4_0)
    | ~ r2_lattice3(esk1_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X23)
        | r1_orders_2(X22,X24,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk6_3(X22,X23,X24),u1_struct_0(X22))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk6_3(X22,X23,X24),X23)
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X24,esk6_3(X22,X23,X24))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_23,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),esk4_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X1)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X1)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_9]),c_0_10])])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk4_0)
    | m1_subset_1(esk6_3(esk1_0,X1,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_10])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk4_0),X1)
    | r1_lattice3(esk1_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_9]),c_0_10])])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X2)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk4_0)
    | ~ r2_lattice3(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk6_3(esk1_0,X2,esk4_0))
    | r1_lattice3(esk1_0,X2,esk4_0)
    | ~ r2_hidden(esk6_3(esk1_0,X2,esk4_0),X3)
    | ~ r1_lattice3(esk1_0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_10])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,k2_xboole_0(X1,X2),esk4_0),X1)
    | r2_hidden(esk6_3(esk1_0,k2_xboole_0(X1,X2),esk4_0),X2)
    | r1_lattice3(esk1_0,k2_xboole_0(X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),esk4_0)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk4_0)
    | ~ r2_lattice3(esk1_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk4_0)
    | ~ r2_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk6_3(esk1_0,k2_xboole_0(X2,X3),esk4_0))
    | r2_hidden(esk6_3(esk1_0,k2_xboole_0(X2,X3),esk4_0),X3)
    | r1_lattice3(esk1_0,k2_xboole_0(X2,X3),esk4_0)
    | ~ r1_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0),esk4_0)
    | r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),esk4_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X1)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk6_3(esk1_0,k2_xboole_0(X1,X2),esk4_0))
    | r2_hidden(esk6_3(esk1_0,k2_xboole_0(X1,X2),esk4_0),X2)
    | r1_lattice3(esk1_0,k2_xboole_0(X1,X2),esk4_0)
    | ~ r1_lattice3(esk1_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_39]),c_0_9]),c_0_10])]),c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X1)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_40]),c_0_9]),c_0_10])])).

cnf(c_0_44,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk6_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk6_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0))
    | r2_hidden(esk6_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X1)
    | r1_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X2)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X1)
    | r1_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_9]),c_0_10])])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),esk4_0)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk1_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk6_3(esk1_0,k2_xboole_0(esk2_0,X2),esk4_0))
    | r1_lattice3(esk1_0,k2_xboole_0(esk2_0,X2),esk4_0)
    | ~ r1_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0),esk4_0)
    | r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk6_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0))
    | r1_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | ~ r1_lattice3(esk1_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_9])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_52]),c_0_9]),c_0_10])]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk1_0,esk4_0,esk6_3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0))
    | r1_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_56,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk4_0)
    | ~ r1_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_55]),c_0_9]),c_0_10])])).

cnf(c_0_58,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),esk4_0)
    | r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X1)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X1)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_59]),c_0_9]),c_0_10])])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),X2)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | ~ r2_lattice3(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0)
    | ~ r1_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0),esk4_0)
    | r2_lattice3(esk1_0,k2_xboole_0(esk2_0,X1),esk4_0)
    | ~ r2_lattice3(esk1_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_9])).

cnf(c_0_65,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_57])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_57])])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk1_0,esk7_3(esk1_0,k2_xboole_0(esk2_0,esk3_0),esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_67]),c_0_9]),c_0_10])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
