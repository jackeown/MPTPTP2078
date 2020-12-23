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
% DateTime   : Thu Dec  3 11:15:11 EST 2020

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
    ! [X9,X10,X11,X12] :
      ( ( ~ r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X12,X10)
        | r1_orders_2(X9,X11,X12)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))
        | r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X10)
        | r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,X11,esk1_3(X9,X10,X11))
        | r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) ) ) ),
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
    ! [X14,X15,X16,X17] :
      ( ( ~ r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X17,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,esk2_3(X14,X15,X16),X16)
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
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
    ! [X5,X6,X7,X8] :
      ( ~ v4_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ r1_orders_2(X5,X6,X7)
      | ~ r1_orders_2(X5,X7,X8)
      | r1_orders_2(X5,X6,X8) ) ),
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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_12]),c_0_9]),c_0_10]),c_0_28])])).

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
    ( r1_lattice3(esk3_0,esk6_0,esk4_0)
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))
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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_43]),c_0_36]),c_0_12]),c_0_10]),c_0_28])])).

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
    ( r1_lattice3(esk3_0,esk6_0,esk5_0)
    | r1_orders_2(esk3_0,X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_45]),c_0_9]),c_0_10])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_9]),c_0_10])]),c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk3_0,esk6_0,esk5_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,esk6_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk3_0,esk6_0,esk5_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(esk3_0,esk6_0,esk4_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0)) ),
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
    ( r1_lattice3(esk3_0,esk6_0,esk5_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattice3(esk3_0,esk6_0,esk4_0)
    | r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_60]),c_0_12])])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_59]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))
    | ~ r1_orders_2(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_62]),c_0_36]),c_0_12]),c_0_10]),c_0_28])])).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S047A
% 0.13/0.40  # and selection function PSelectComplexPreferNEQ.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.027 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t4_yellow_0, conjecture, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>![X4]:((r1_lattice3(X1,X4,X3)=>r1_lattice3(X1,X4,X2))&(r2_lattice3(X1,X4,X2)=>r2_lattice3(X1,X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_0)).
% 0.13/0.40  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.13/0.40  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.40  fof(t26_orders_2, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 0.13/0.40  fof(c_0_4, negated_conjecture, ~(![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>![X4]:((r1_lattice3(X1,X4,X3)=>r1_lattice3(X1,X4,X2))&(r2_lattice3(X1,X4,X2)=>r2_lattice3(X1,X4,X3)))))))), inference(assume_negation,[status(cth)],[t4_yellow_0])).
% 0.13/0.40  fof(c_0_5, plain, ![X9, X10, X11, X12]:((~r1_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X10)|r1_orders_2(X9,X11,X12)))|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))|r1_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((r2_hidden(esk1_3(X9,X10,X11),X10)|r1_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&(~r1_orders_2(X9,X11,esk1_3(X9,X10,X11))|r1_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.13/0.40  fof(c_0_6, negated_conjecture, ((v4_orders_2(esk3_0)&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(r1_orders_2(esk3_0,esk4_0,esk5_0)&(((r2_lattice3(esk3_0,esk6_0,esk4_0)|r1_lattice3(esk3_0,esk6_0,esk5_0))&(~r2_lattice3(esk3_0,esk6_0,esk5_0)|r1_lattice3(esk3_0,esk6_0,esk5_0)))&((r2_lattice3(esk3_0,esk6_0,esk4_0)|~r1_lattice3(esk3_0,esk6_0,esk4_0))&(~r2_lattice3(esk3_0,esk6_0,esk5_0)|~r1_lattice3(esk3_0,esk6_0,esk4_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.13/0.40  fof(c_0_7, plain, ![X14, X15, X16, X17]:((~r2_lattice3(X14,X15,X16)|(~m1_subset_1(X17,u1_struct_0(X14))|(~r2_hidden(X17,X15)|r1_orders_2(X14,X17,X16)))|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((m1_subset_1(esk2_3(X14,X15,X16),u1_struct_0(X14))|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((r2_hidden(esk2_3(X14,X15,X16),X15)|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&(~r1_orders_2(X14,esk2_3(X14,X15,X16),X16)|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.40  cnf(c_0_8, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.40  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_10, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_11, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_13, negated_conjecture, (r2_lattice3(esk3_0,esk6_0,esk4_0)|~r1_lattice3(esk3_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_14, negated_conjecture, (r1_lattice3(esk3_0,X1,esk4_0)|m1_subset_1(esk1_3(esk3_0,X1,esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])).
% 0.13/0.40  cnf(c_0_15, negated_conjecture, (~r2_lattice3(esk3_0,esk6_0,esk5_0)|~r1_lattice3(esk3_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_16, negated_conjecture, (r2_lattice3(esk3_0,X1,esk5_0)|m1_subset_1(esk2_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_10])])).
% 0.13/0.40  cnf(c_0_17, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_18, negated_conjecture, (r2_lattice3(esk3_0,esk6_0,esk4_0)|m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.40  cnf(c_0_20, negated_conjecture, (r1_orders_2(esk3_0,X1,esk4_0)|m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_9]), c_0_10])])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))|m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_14])).
% 0.13/0.40  cnf(c_0_22, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  fof(c_0_23, plain, ![X5, X6, X7, X8]:(~v4_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|(~m1_subset_1(X7,u1_struct_0(X5))|(~m1_subset_1(X8,u1_struct_0(X5))|(~r1_orders_2(X5,X6,X7)|~r1_orders_2(X5,X7,X8)|r1_orders_2(X5,X6,X8)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)|m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))|~r2_hidden(esk2_3(esk3_0,esk6_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (r2_lattice3(esk3_0,X1,esk5_0)|r2_hidden(esk2_3(esk3_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_12]), c_0_10])])).
% 0.13/0.40  cnf(c_0_26, plain, (r1_orders_2(X1,X2,X4)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (r2_lattice3(esk3_0,esk6_0,esk5_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)|m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (r1_orders_2(esk3_0,X1,esk5_0)|~r1_orders_2(esk3_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_12]), c_0_9]), c_0_10]), c_0_28])])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)|m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_29]), c_0_14])).
% 0.13/0.40  cnf(c_0_32, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk5_0)|m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_21])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (r2_lattice3(esk3_0,esk6_0,esk5_0)|m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_12]), c_0_10])])).
% 0.13/0.40  cnf(c_0_35, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk6_0,esk4_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_34]), c_0_14])).
% 0.13/0.40  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))|~r2_hidden(esk1_3(esk3_0,esk6_0,esk4_0),X2)|~r1_lattice3(esk3_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_10])])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_3(esk3_0,X1,esk4_0),X1)|r1_lattice3(esk3_0,X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_9]), c_0_10])])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk5_0)|~r2_lattice3(esk3_0,esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk4_0)|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))|~r1_lattice3(esk3_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk5_0)|m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_16])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))|m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_12])]), c_0_19])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))|m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0))|~r1_orders_2(esk3_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_43]), c_0_36]), c_0_12]), c_0_10]), c_0_28])])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (r2_lattice3(esk3_0,esk6_0,esk4_0)|r1_lattice3(esk3_0,esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_46, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,esk6_0,esk4_0))|m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_9])])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk5_0)|r1_orders_2(esk3_0,X1,esk4_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_45]), c_0_9]), c_0_10])])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk6_0,esk5_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_9]), c_0_10])]), c_0_19])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk5_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)|~r2_hidden(esk2_3(esk3_0,esk6_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk5_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_25]), c_0_40])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk4_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_51]), c_0_12])])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (r2_lattice3(esk3_0,esk6_0,esk4_0)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))|r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_52])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))|r1_orders_2(esk3_0,X1,esk4_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_53]), c_0_9]), c_0_10])])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))|~r2_hidden(esk2_3(esk3_0,esk6_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_54]), c_0_49])])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (r2_lattice3(esk3_0,esk6_0,esk5_0)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))|r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_25])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_56]), c_0_52])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))|r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_57]), c_0_49])])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (r2_lattice3(esk3_0,esk6_0,esk5_0)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_58]), c_0_12]), c_0_10])])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk5_0)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_59])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk4_0)|r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_60]), c_0_12])])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk1_3(esk3_0,esk6_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_59]), c_0_61])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk6_0,esk4_0))|~r1_orders_2(esk3_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_62]), c_0_36]), c_0_12]), c_0_10]), c_0_28])])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk1_3(esk3_0,esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_27]), c_0_9])])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (r1_lattice3(esk3_0,esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_64]), c_0_9]), c_0_10])])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (r2_lattice3(esk3_0,esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_65])])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (r1_orders_2(esk3_0,X1,esk4_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_66]), c_0_9]), c_0_10])])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)|~r2_hidden(esk2_3(esk3_0,esk6_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_67, c_0_49])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (~r2_lattice3(esk3_0,esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_65])])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_25]), c_0_69])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk6_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_70]), c_0_49])])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_71]), c_0_12]), c_0_10])]), c_0_69]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 73
% 0.13/0.40  # Proof object clause steps            : 64
% 0.13/0.40  # Proof object formula steps           : 9
% 0.13/0.40  # Proof object conjectures             : 58
% 0.13/0.40  # Proof object clause conjectures      : 55
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 18
% 0.13/0.40  # Proof object initial formulas used   : 4
% 0.13/0.40  # Proof object generating inferences   : 44
% 0.13/0.40  # Proof object simplifying inferences  : 82
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 4
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 18
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 18
% 0.13/0.40  # Processed clauses                    : 295
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 44
% 0.13/0.40  # ...remaining for further processing  : 251
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 85
% 0.13/0.40  # Backward-rewritten                   : 59
% 0.13/0.40  # Generated clauses                    : 458
% 0.13/0.40  # ...of the previous two non-trivial   : 440
% 0.13/0.40  # Contextual simplify-reflections      : 17
% 0.13/0.40  # Paramodulations                      : 450
% 0.13/0.40  # Factorizations                       : 4
% 0.13/0.40  # Equation resolutions                 : 0
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 85
% 0.13/0.40  #    Positive orientable unit clauses  : 16
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 1
% 0.13/0.40  #    Non-unit-clauses                  : 68
% 0.13/0.40  # Current number of unprocessed clauses: 124
% 0.13/0.40  # ...number of literals in the above   : 498
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 166
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 4432
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 2039
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 119
% 0.13/0.40  # Unit Clause-clause subsumption calls : 255
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 35
% 0.13/0.40  # BW rewrite match successes           : 10
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 12275
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.050 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.057 s
% 0.13/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
