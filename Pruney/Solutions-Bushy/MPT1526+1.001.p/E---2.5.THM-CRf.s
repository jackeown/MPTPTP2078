%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1526+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:20 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   73 (16599 expanded)
%              Number of clauses        :   64 (5906 expanded)
%              Number of leaves         :    4 (3911 expanded)
%              Depth                    :   40
%              Number of atoms          :  257 (125841 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_yellow_0,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
               => ! [X4] :
                    ( ( r1_lattice3(X1,X4,X3)
                     => r1_lattice3(X1,X4,X2) )
                    & ( r2_lattice3(X1,X4,X2)
                     => r2_lattice3(X1,X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

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

fof(t26_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_orders_2(X1,X2,X3)
                 => ! [X4] :
                      ( ( r1_lattice3(X1,X4,X3)
                       => r1_lattice3(X1,X4,X2) )
                      & ( r2_lattice3(X1,X4,X2)
                       => r2_lattice3(X1,X4,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_yellow_0])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_hidden(X8,X6)
        | r1_orders_2(X5,X7,X8)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X7,esk1_3(X5,X6,X7))
        | r1_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_6,negated_conjecture,
    ( v4_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & r1_orders_2(esk3_0,esk4_0,esk5_0)
    & ( r2_lattice3(esk3_0,esk6_0,esk4_0)
      | r1_lattice3(esk3_0,esk6_0,esk5_0) )
    & ( ~ r2_lattice3(esk3_0,esk6_0,esk5_0)
      | r1_lattice3(esk3_0,esk6_0,esk5_0) )
    & ( r2_lattice3(esk3_0,esk6_0,esk4_0)
      | ~ r1_lattice3(esk3_0,esk6_0,esk4_0) )
    & ( ~ r2_lattice3(esk3_0,esk6_0,esk5_0)
      | ~ r1_lattice3(esk3_0,esk6_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X11)
        | r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_3(X10,X11,X12),u1_struct_0(X10))
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r2_hidden(esk2_3(X10,X11,X12),X11)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk2_3(X10,X11,X12),X12)
        | r2_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r2_lattice3(esk3_0,esk6_0,esk4_0)
    | ~ r1_lattice3(esk3_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk6_0,esk5_0)
    | ~ r1_lattice3(esk3_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_10])])).

cnf(c_0_17,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( r2_lattice3(esk3_0,esk6_0,esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_9]),c_0_10])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_23,plain,(
    ! [X15,X16,X17,X18] :
      ( ~ v4_orders_2(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | ~ m1_subset_1(X18,u1_struct_0(X15))
      | ~ r1_orders_2(X15,X16,X17)
      | ~ r1_orders_2(X15,X17,X18)
      | r1_orders_2(X15,X16,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk6_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk5_0)
    | r2_hidden(esk2_3(esk3_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_12]),c_0_10])])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk3_0,esk6_0,esk5_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk5_0)
    | ~ r1_orders_2(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_12]),c_0_9]),c_0_10])])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_29]),c_0_14])).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(esk3_0,esk6_0,esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_12]),c_0_10])])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_34]),c_0_14])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk6_0,esk4_0),X2)
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_10])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,esk4_0),X1)
    | r1_lattice3(esk3_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_9]),c_0_10])])).

cnf(c_0_40,negated_conjecture,
    ( r1_lattice3(esk3_0,esk6_0,esk5_0)
    | ~ r2_lattice3(esk3_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))
    | r1_lattice3(esk3_0,esk6_0,esk4_0)
    | ~ r1_lattice3(esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattice3(esk3_0,esk6_0,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_12])]),c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))
    | m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_orders_2(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_43]),c_0_28]),c_0_36]),c_0_12]),c_0_10])])).

cnf(c_0_45,negated_conjecture,
    ( r2_lattice3(esk3_0,esk6_0,esk4_0)
    | r1_lattice3(esk3_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_46,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_9])])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk4_0)
    | r1_lattice3(esk3_0,esk6_0,esk5_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_45]),c_0_9]),c_0_10])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_9]),c_0_10])]),c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | r1_lattice3(esk3_0,esk6_0,esk5_0)
    | ~ r2_hidden(esk2_3(esk3_0,esk6_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | r1_lattice3(esk3_0,esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | r1_lattice3(esk3_0,esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_51]),c_0_12])])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk3_0,esk6_0,esk4_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | r1_orders_2(esk3_0,X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_53]),c_0_9]),c_0_10])])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk6_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_54]),c_0_49])])).

cnf(c_0_56,negated_conjecture,
    ( r2_lattice3(esk3_0,esk6_0,esk5_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_25])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_56]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_57]),c_0_49])])).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk3_0,esk6_0,esk5_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_58]),c_0_12]),c_0_10])])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | r1_lattice3(esk3_0,esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))
    | r1_lattice3(esk3_0,esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_60]),c_0_12])])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_59]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))
    | ~ r1_orders_2(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_62]),c_0_28]),c_0_36]),c_0_12]),c_0_10])])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_27]),c_0_9])])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(esk3_0,esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_64]),c_0_9]),c_0_10])])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk3_0,esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_65])])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_66]),c_0_9]),c_0_10])])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,esk6_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_49])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_65])])).

cnf(c_0_70,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_25]),c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_70]),c_0_49])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_71]),c_0_12]),c_0_10])]),c_0_69]),
    [proof]).

%------------------------------------------------------------------------------
