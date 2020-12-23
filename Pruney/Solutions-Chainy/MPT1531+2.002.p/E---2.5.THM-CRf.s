%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:13 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 (3372 expanded)
%              Number of clauses        :   66 (1261 expanded)
%              Number of leaves         :    4 ( 783 expanded)
%              Depth                    :   36
%              Number of atoms          :  238 (21571 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,X3,X4)
                 => r1_lattice3(X1,X2,X4) )
                & ( r2_lattice3(X1,X3,X4)
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( ( r1_lattice3(X1,X3,X4)
                   => r1_lattice3(X1,X2,X4) )
                  & ( r2_lattice3(X1,X3,X4)
                   => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_yellow_0])).

fof(c_0_5,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r2_hidden(X19,X17)
        | r1_orders_2(X16,X19,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk3_3(X16,X17,X18),u1_struct_0(X16))
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X17)
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,esk3_3(X16,X17,X18),X18)
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_6,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & r1_tarski(esk5_0,esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & ( r2_lattice3(esk4_0,esk6_0,esk7_0)
      | r1_lattice3(esk4_0,esk6_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
      | r1_lattice3(esk4_0,esk6_0,esk7_0) )
    & ( r2_lattice3(esk4_0,esk6_0,esk7_0)
      | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) )
    & ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
      | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
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
    ! [X11,X12,X13,X14] :
      ( ( ~ r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X14,X12)
        | r1_orders_2(X11,X13,X14)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk2_3(X11,X12,X13),u1_struct_0(X11))
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X12)
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,X13,esk2_3(X11,X12,X13))
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk7_0)
    | r2_hidden(esk3_3(esk4_0,X1,esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk7_0)
    | m1_subset_1(esk3_3(esk4_0,X1,esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_8]),c_0_9])])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk7_0)
    | m1_subset_1(esk2_3(esk4_0,X1,esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9])])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_9])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | ~ r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),esk7_0)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_8])])).

cnf(c_0_34,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk7_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_8]),c_0_9])])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0)
    | m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_8]),c_0_9])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_34])).

cnf(c_0_37,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_35]),c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk2_3(esk4_0,esk5_0,esk7_0))
    | ~ r1_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_9])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattice3(esk4_0,esk6_0,esk7_0)
    | ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk2_3(esk4_0,esk5_0,esk7_0))
    | m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(esk4_0,esk6_0,esk7_0)
    | m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_15])).

cnf(c_0_45,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,esk5_0,esk7_0))
    | m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_8])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)
    | r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_8]),c_0_9])]),c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)
    | r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)
    | ~ r2_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_48]),c_0_9])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk6_0)
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)
    | ~ r2_lattice3(esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),esk7_0)
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_8])])).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(esk4_0,esk5_0,esk7_0)
    | r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_54]),c_0_8]),c_0_9])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_55]),c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk2_3(esk4_0,esk5_0,esk7_0))
    | ~ r1_lattice3(esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( r1_lattice3(esk4_0,esk6_0,esk7_0)
    | r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_13])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,esk5_0,esk7_0))
    | r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_8])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_61]),c_0_8]),c_0_9])]),c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)
    | ~ r2_lattice3(esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | r1_lattice3(esk4_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),esk7_0)
    | r1_lattice3(esk4_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_8])])).

cnf(c_0_68,negated_conjecture,
    ( r1_lattice3(esk4_0,esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_67]),c_0_8]),c_0_9])]),c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_68]),c_0_8])])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_69]),c_0_8]),c_0_9])])).

cnf(c_0_71,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_70])])).

cnf(c_0_72,negated_conjecture,
    ( r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_71]),c_0_8])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_70])])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_72]),c_0_8]),c_0_9])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:55:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EA
% 0.21/0.41  # and selection function SelectLComplex.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.037 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t9_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 0.21/0.41  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.21/0.41  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.21/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.41  fof(c_0_4, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t9_yellow_0])).
% 0.21/0.41  fof(c_0_5, plain, ![X16, X17, X18, X19]:((~r2_lattice3(X16,X17,X18)|(~m1_subset_1(X19,u1_struct_0(X16))|(~r2_hidden(X19,X17)|r1_orders_2(X16,X19,X18)))|~m1_subset_1(X18,u1_struct_0(X16))|~l1_orders_2(X16))&((m1_subset_1(esk3_3(X16,X17,X18),u1_struct_0(X16))|r2_lattice3(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~l1_orders_2(X16))&((r2_hidden(esk3_3(X16,X17,X18),X17)|r2_lattice3(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~l1_orders_2(X16))&(~r1_orders_2(X16,esk3_3(X16,X17,X18),X18)|r2_lattice3(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~l1_orders_2(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.21/0.41  fof(c_0_6, negated_conjecture, (l1_orders_2(esk4_0)&(r1_tarski(esk5_0,esk6_0)&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(((r2_lattice3(esk4_0,esk6_0,esk7_0)|r1_lattice3(esk4_0,esk6_0,esk7_0))&(~r2_lattice3(esk4_0,esk5_0,esk7_0)|r1_lattice3(esk4_0,esk6_0,esk7_0)))&((r2_lattice3(esk4_0,esk6_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0))&(~r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.21/0.41  cnf(c_0_7, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.41  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.41  cnf(c_0_9, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.41  fof(c_0_10, plain, ![X11, X12, X13, X14]:((~r1_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X12)|r1_orders_2(X11,X13,X14)))|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&((m1_subset_1(esk2_3(X11,X12,X13),u1_struct_0(X11))|r1_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&((r2_hidden(esk2_3(X11,X12,X13),X12)|r1_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))&(~r1_orders_2(X11,X13,esk2_3(X11,X12,X13))|r1_lattice3(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~l1_orders_2(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.21/0.41  cnf(c_0_11, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.41  cnf(c_0_12, negated_conjecture, (~r2_lattice3(esk4_0,esk5_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.41  cnf(c_0_13, negated_conjecture, (r2_lattice3(esk4_0,X1,esk7_0)|r2_hidden(esk3_3(esk4_0,X1,esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])])).
% 0.21/0.41  cnf(c_0_14, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_15, negated_conjecture, (r2_lattice3(esk4_0,X1,esk7_0)|m1_subset_1(esk3_3(esk4_0,X1,esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_8]), c_0_9])])).
% 0.21/0.41  fof(c_0_16, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.41  cnf(c_0_17, negated_conjecture, (r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.41  cnf(c_0_18, negated_conjecture, (r1_lattice3(esk4_0,X1,esk7_0)|m1_subset_1(esk2_3(esk4_0,X1,esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_8]), c_0_9])])).
% 0.21/0.41  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_12, c_0_15])).
% 0.21/0.41  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.41  cnf(c_0_22, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.41  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.21/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.41  cnf(c_0_25, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.41  cnf(c_0_26, negated_conjecture, (r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)|m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_9])])).
% 0.21/0.41  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.41  cnf(c_0_28, negated_conjecture, (r2_lattice3(esk4_0,esk6_0,esk7_0)|~r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.41  cnf(c_0_29, negated_conjecture, (r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)|m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.41  cnf(c_0_30, negated_conjecture, (r2_lattice3(esk4_0,esk6_0,esk7_0)|m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.21/0.41  cnf(c_0_31, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_32, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.41  cnf(c_0_33, negated_conjecture, (r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),esk7_0)|m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_8])])).
% 0.21/0.41  cnf(c_0_34, negated_conjecture, (r1_lattice3(esk4_0,X1,esk7_0)|r2_hidden(esk2_3(esk4_0,X1,esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_8]), c_0_9])])).
% 0.21/0.41  cnf(c_0_35, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk7_0)|m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_8]), c_0_9])])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_34])).
% 0.21/0.41  cnf(c_0_37, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk2_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_35]), c_0_18])).
% 0.21/0.41  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_36])).
% 0.21/0.41  cnf(c_0_40, negated_conjecture, (r1_orders_2(esk4_0,X1,esk2_3(esk4_0,esk5_0,esk7_0))|~r1_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_9])])).
% 0.21/0.41  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 0.21/0.41  cnf(c_0_42, negated_conjecture, (r1_lattice3(esk4_0,esk6_0,esk7_0)|~r2_lattice3(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.41  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk4_0,X1,esk2_3(esk4_0,esk5_0,esk7_0))|m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))|~r1_lattice3(esk4_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.41  cnf(c_0_44, negated_conjecture, (r1_lattice3(esk4_0,esk6_0,esk7_0)|m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_15])).
% 0.21/0.41  cnf(c_0_45, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,esk5_0,esk7_0))|m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_8])])).
% 0.21/0.41  cnf(c_0_47, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)|r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_34])).
% 0.21/0.41  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk3_3(esk4_0,esk5_0,esk7_0),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_8]), c_0_9])]), c_0_19])).
% 0.21/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)|r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_47])).
% 0.21/0.41  cnf(c_0_50, negated_conjecture, (r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)|~r2_lattice3(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_48]), c_0_9])])).
% 0.21/0.41  cnf(c_0_51, negated_conjecture, (r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk6_0)|r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_25])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)|r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)|~r2_lattice3(esk4_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.41  cnf(c_0_53, negated_conjecture, (r2_lattice3(esk4_0,esk6_0,esk7_0)|r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 0.21/0.41  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),esk7_0)|r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_8])])).
% 0.21/0.41  cnf(c_0_55, negated_conjecture, (r2_lattice3(esk4_0,esk5_0,esk7_0)|r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_54]), c_0_8]), c_0_9])])).
% 0.21/0.41  cnf(c_0_56, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_55]), c_0_34])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_56])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_25])).
% 0.21/0.41  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk4_0,X1,esk2_3(esk4_0,esk5_0,esk7_0))|~r1_lattice3(esk4_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_58])).
% 0.21/0.41  cnf(c_0_60, negated_conjecture, (r1_lattice3(esk4_0,esk6_0,esk7_0)|r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_13])).
% 0.21/0.41  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,esk5_0,esk7_0))|r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_8])])).
% 0.21/0.41  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_61]), c_0_8]), c_0_9])]), c_0_17])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_62])).
% 0.21/0.41  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_3(esk4_0,esk5_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_25])).
% 0.21/0.41  cnf(c_0_65, negated_conjecture, (r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),X1)|~r2_lattice3(esk4_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_64])).
% 0.21/0.41  cnf(c_0_66, negated_conjecture, (r2_lattice3(esk4_0,esk6_0,esk7_0)|r1_lattice3(esk4_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.41  cnf(c_0_67, negated_conjecture, (r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),esk7_0)|r1_lattice3(esk4_0,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_8])])).
% 0.21/0.41  cnf(c_0_68, negated_conjecture, (r1_lattice3(esk4_0,esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_67]), c_0_8]), c_0_9])]), c_0_42])).
% 0.21/0.41  cnf(c_0_69, negated_conjecture, (r1_orders_2(esk4_0,esk7_0,esk2_3(esk4_0,esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_68]), c_0_8])])).
% 0.21/0.41  cnf(c_0_70, negated_conjecture, (r1_lattice3(esk4_0,esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_69]), c_0_8]), c_0_9])])).
% 0.21/0.41  cnf(c_0_71, negated_conjecture, (r2_lattice3(esk4_0,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_70])])).
% 0.21/0.41  cnf(c_0_72, negated_conjecture, (r1_orders_2(esk4_0,esk3_3(esk4_0,esk5_0,esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_71]), c_0_8])])).
% 0.21/0.41  cnf(c_0_73, negated_conjecture, (~r2_lattice3(esk4_0,esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_70])])).
% 0.21/0.41  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_72]), c_0_8]), c_0_9])]), c_0_73]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 75
% 0.21/0.41  # Proof object clause steps            : 66
% 0.21/0.41  # Proof object formula steps           : 9
% 0.21/0.41  # Proof object conjectures             : 60
% 0.21/0.41  # Proof object clause conjectures      : 57
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 16
% 0.21/0.41  # Proof object initial formulas used   : 4
% 0.21/0.41  # Proof object generating inferences   : 48
% 0.21/0.41  # Proof object simplifying inferences  : 59
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 4
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 18
% 0.21/0.41  # Removed in clause preprocessing      : 0
% 0.21/0.41  # Initial clauses in saturation        : 18
% 0.21/0.41  # Processed clauses                    : 200
% 0.21/0.41  # ...of these trivial                  : 0
% 0.21/0.41  # ...subsumed                          : 11
% 0.21/0.41  # ...remaining for further processing  : 189
% 0.21/0.41  # Other redundant clauses eliminated   : 0
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 21
% 0.21/0.41  # Backward-rewritten                   : 78
% 0.21/0.41  # Generated clauses                    : 314
% 0.21/0.41  # ...of the previous two non-trivial   : 297
% 0.21/0.41  # Contextual simplify-reflections      : 5
% 0.21/0.41  # Paramodulations                      : 310
% 0.21/0.41  # Factorizations                       : 4
% 0.21/0.41  # Equation resolutions                 : 0
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 72
% 0.21/0.41  #    Positive orientable unit clauses  : 16
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 1
% 0.21/0.41  #    Non-unit-clauses                  : 55
% 0.21/0.41  # Current number of unprocessed clauses: 88
% 0.21/0.41  # ...number of literals in the above   : 240
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 117
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 1592
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 785
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 25
% 0.21/0.41  # Unit Clause-clause subsumption calls : 214
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 23
% 0.21/0.41  # BW rewrite match successes           : 12
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 8790
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.060 s
% 0.21/0.41  # System time              : 0.004 s
% 0.21/0.41  # Total time               : 0.064 s
% 0.21/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
