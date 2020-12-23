%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   59 (1621 expanded)
%              Number of clauses        :   48 ( 608 expanded)
%              Number of leaves         :    5 ( 381 expanded)
%              Depth                    :   24
%              Number of atoms          :  205 (10052 expanded)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X16)
        | r1_orders_2(X15,X18,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X16)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,esk2_3(X15,X16,X17),X17)
        | r2_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_7,negated_conjecture,
    ( l1_orders_2(esk3_0)
    & r1_tarski(esk4_0,esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r2_lattice3(esk3_0,esk5_0,esk6_0)
      | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) )
    & ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
      | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r1_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X11)
        | r1_orders_2(X10,X12,X13)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X12),u1_struct_0(X10))
        | r1_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r1_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,X12,esk1_3(X10,X11,X12))
        | r1_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_9]),c_0_10])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_9]),c_0_10])])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_10])])).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_33,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_9])])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_10]),c_0_9])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_35]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_9]),c_0_10])])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_10])])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk6_0)
    | r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_14])).

cnf(c_0_45,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_9])]),c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_10]),c_0_9])]),c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | ~ r2_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_47]),c_0_10])])).

cnf(c_0_49,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)
    | ~ r2_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_9])]),c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_51]),c_0_10]),c_0_9])]),c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_52]),c_0_9])])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_53]),c_0_10]),c_0_9])])).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_54])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_54])])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_55]),c_0_9])]),c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_57]),c_0_10]),c_0_9])]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:03:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EA
% 0.13/0.37  # and selection function SelectLComplex.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t9_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 0.13/0.37  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.37  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.13/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t9_yellow_0])).
% 0.13/0.37  fof(c_0_6, plain, ![X15, X16, X17, X18]:((~r2_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X16)|r1_orders_2(X15,X18,X17)))|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((m1_subset_1(esk2_3(X15,X16,X17),u1_struct_0(X15))|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&((r2_hidden(esk2_3(X15,X16,X17),X16)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))&(~r1_orders_2(X15,esk2_3(X15,X16,X17),X17)|r2_lattice3(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~l1_orders_2(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, (l1_orders_2(esk3_0)&(r1_tarski(esk4_0,esk5_0)&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(((r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0))&(~r2_lattice3(esk3_0,esk4_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)))&((r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk3_0,esk4_0,esk6_0))&(~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r1_lattice3(esk3_0,esk4_0,esk6_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.37  cnf(c_0_8, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  fof(c_0_11, plain, ![X10, X11, X12, X13]:((~r1_lattice3(X10,X11,X12)|(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_hidden(X13,X11)|r1_orders_2(X10,X12,X13)))|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&((m1_subset_1(esk1_3(X10,X11,X12),u1_struct_0(X10))|r1_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&((r2_hidden(esk1_3(X10,X11,X12),X11)|r1_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))&(~r1_orders_2(X10,X12,esk1_3(X10,X11,X12))|r1_lattice3(X10,X11,X12)|~m1_subset_1(X12,u1_struct_0(X10))|~l1_orders_2(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.13/0.37  fof(c_0_12, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk2_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])).
% 0.13/0.37  cnf(c_0_15, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  fof(c_0_16, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.13/0.37  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_9]), c_0_10])])).
% 0.13/0.37  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_23, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_24, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk2_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_9]), c_0_10])])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,X2,X1)|~r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_10])])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|~r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r2_lattice3(esk3_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.13/0.37  cnf(c_0_33, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_9])])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_10]), c_0_9])])).
% 0.13/0.37  cnf(c_0_36, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_37, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_35]), c_0_20])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_9]), c_0_10])])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_lattice3(esk3_0,X2,X1)|~r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_10])])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r1_lattice3(esk3_0,esk4_0,esk6_0)|r2_hidden(esk1_3(esk3_0,esk4_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|r1_lattice3(esk3_0,esk4_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_14])).
% 0.13/0.37  cnf(c_0_45, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_9])]), c_0_19])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_10]), c_0_9])]), c_0_19])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)|~r2_lattice3(esk3_0,X2,X1)|~r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_47]), c_0_10])])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),X1)|~r2_lattice3(esk3_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_29])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_9])]), c_0_42])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_51]), c_0_10]), c_0_9])]), c_0_42])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_52]), c_0_9])])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_53]), c_0_10]), c_0_9])])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_54])])).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, (~r2_lattice3(esk3_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_54])])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk3_0,esk2_3(esk3_0,esk4_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_55]), c_0_9])]), c_0_56])).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_57]), c_0_10]), c_0_9])]), c_0_56]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 59
% 0.13/0.37  # Proof object clause steps            : 48
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 41
% 0.13/0.37  # Proof object clause conjectures      : 38
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 17
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 29
% 0.13/0.37  # Proof object simplifying inferences  : 50
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 18
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 18
% 0.13/0.37  # Processed clauses                    : 130
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 8
% 0.13/0.37  # ...remaining for further processing  : 121
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 11
% 0.13/0.37  # Backward-rewritten                   : 34
% 0.13/0.37  # Generated clauses                    : 137
% 0.13/0.37  # ...of the previous two non-trivial   : 133
% 0.13/0.37  # Contextual simplify-reflections      : 5
% 0.13/0.37  # Paramodulations                      : 135
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 56
% 0.13/0.37  #    Positive orientable unit clauses  : 11
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 44
% 0.13/0.37  # Current number of unprocessed clauses: 29
% 0.13/0.37  # ...number of literals in the above   : 87
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 65
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 912
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 495
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 21
% 0.13/0.37  # Unit Clause-clause subsumption calls : 66
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 12
% 0.13/0.37  # BW rewrite match successes           : 6
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 5205
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.036 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.039 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
