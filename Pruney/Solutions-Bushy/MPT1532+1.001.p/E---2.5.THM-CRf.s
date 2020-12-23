%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1532+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  100 (25123 expanded)
%              Number of clauses        :   91 (9623 expanded)
%              Number of leaves         :    4 (5797 expanded)
%              Depth                    :   33
%              Number of atoms          :  328 (207845 expanded)
%              Number of equality atoms :   10 (2648 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

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
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r2_hidden(X22,X20)
        | r1_orders_2(X19,X22,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( m1_subset_1(esk3_3(X19,X20,X21),u1_struct_0(X19))
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( r2_hidden(esk3_3(X19,X20,X21),X20)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r1_orders_2(X19,esk3_3(X19,X20,X21),X21)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_6,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & ( r2_lattice3(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( r2_lattice3(esk4_0,esk6_0,esk7_0)
      | r1_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0)
      | r1_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( r2_lattice3(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,esk6_0,esk7_0) )
    & ( r2_lattice3(esk4_0,esk6_0,esk7_0)
      | r1_lattice3(esk4_0,esk6_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0)
      | r1_lattice3(esk4_0,esk6_0,esk7_0) )
    & ( r2_lattice3(esk4_0,esk5_0,esk7_0)
      | ~ r1_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) )
    & ( r2_lattice3(esk4_0,esk6_0,esk7_0)
      | ~ r1_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) )
    & ( ~ r2_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0)
      | ~ r1_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,X16,esk2_3(X14,X15,X16))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0)
    | ~ r1_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk7_0)
    | m1_subset_1(esk3_3(esk4_0,X1,esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk7_0)
    | r2_hidden(esk3_3(esk4_0,X1,esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_8]),c_0_9])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk7_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0))
    | ~ r1_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | ~ r1_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0))
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r1_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),X1)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0))
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_9])])).

cnf(c_0_28,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0))
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0)
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0))
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_8])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0)
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0))
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_32]),c_0_8])])).

cnf(c_0_40,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk7_0)
    | m1_subset_1(esk2_3(esk4_0,X1,esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_8]),c_0_9])])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk7_0)
    | ~ r1_orders_2(esk4_0,esk3_3(esk4_0,X1,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_8]),c_0_9])])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_43,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk4_0,esk6_0,esk7_0)
    | ~ r2_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r2_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0))
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_9])])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattice3(esk4_0,esk6_0,esk7_0)
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_46]),c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk7_0)
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_16])).

cnf(c_0_52,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_8])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0)
    | r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_51]),c_0_8])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk7_0)
    | ~ r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,X1,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_8]),c_0_9])])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),X1)
    | m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_56]),c_0_9])])).

cnf(c_0_60,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),k2_xboole_0(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0)
    | m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_8])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0)
    | r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_62]),c_0_8])])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( r2_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0)
    | m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_67]),c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_68]),c_0_9])])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattice3(esk4_0,esk6_0,esk7_0)
    | m1_subset_1(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_13])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk7_0)
    | m1_subset_1(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | m1_subset_1(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_8])])).

cnf(c_0_73,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | m1_subset_1(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_71]),c_0_8])])).

cnf(c_0_74,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | m1_subset_1(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_54]),c_0_73])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_74]),c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_75]),c_0_9])])).

cnf(c_0_77,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | r1_lattice3(esk4_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_78,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0)
    | r1_lattice3(esk4_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_79,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_80,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0)
    | r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_81,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | r1_lattice3(esk4_0,esk6_0,esk7_0)
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_8])])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | r1_lattice3(esk4_0,esk6_0,esk7_0)
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_78]),c_0_8])])).

cnf(c_0_83,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | r1_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_79]),c_0_8])])).

cnf(c_0_84,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | r1_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_80]),c_0_8])])).

cnf(c_0_85,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | r1_lattice3(esk4_0,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_64]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_64]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( r1_lattice3(esk4_0,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_85]),c_0_45])).

cnf(c_0_88,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_86]),c_0_47])).

cnf(c_0_89,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_87]),c_0_8])])).

cnf(c_0_90,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0))
    | ~ r2_hidden(esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_88]),c_0_8])])).

cnf(c_0_91,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_54]),c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( r1_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_92])])).

cnf(c_0_94,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_92])])).

cnf(c_0_95,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_93]),c_0_8])])).

cnf(c_0_96,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0)
    | ~ r2_hidden(esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_94]),c_0_8])])).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_64]),c_0_96])).

cnf(c_0_98,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k2_xboole_0(esk5_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_92])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_97]),c_0_98]),
    [proof]).

%------------------------------------------------------------------------------
