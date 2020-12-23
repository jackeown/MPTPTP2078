%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t4_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:44 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   77 (12037 expanded)
%              Number of clauses        :   68 (4302 expanded)
%              Number of leaves         :    4 (2828 expanded)
%              Depth                    :   32
%              Number of atoms          :  259 (90857 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',t4_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',d8_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',d9_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',t26_orders_2)).

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
    ! [X11,X12,X13,X14] :
      ( ( ~ r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X14,X12)
        | r1_orders_2(X11,X13,X14)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk5_3(X11,X12,X13),u1_struct_0(X11))
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk5_3(X11,X12,X13),X12)
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,X13,esk5_3(X11,X12,X13))
        | r1_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_6,negated_conjecture,
    ( v4_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & r1_orders_2(esk1_0,esk2_0,esk3_0)
    & ( r2_lattice3(esk1_0,esk4_0,esk2_0)
      | r1_lattice3(esk1_0,esk4_0,esk3_0) )
    & ( ~ r2_lattice3(esk1_0,esk4_0,esk3_0)
      | r1_lattice3(esk1_0,esk4_0,esk3_0) )
    & ( r2_lattice3(esk1_0,esk4_0,esk2_0)
      | ~ r1_lattice3(esk1_0,esk4_0,esk2_0) )
    & ( ~ r2_lattice3(esk1_0,esk4_0,esk3_0)
      | ~ r1_lattice3(esk1_0,esk4_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r2_hidden(X19,X17)
        | r1_orders_2(X16,X19,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk6_3(X16,X17,X18),u1_struct_0(X16))
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk6_3(X16,X17,X18),X17)
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,esk6_3(X16,X17,X18),X18)
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_11,negated_conjecture,
    ( r2_lattice3(esk1_0,esk4_0,esk2_0)
    | ~ r1_lattice3(esk1_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk2_0)
    | m1_subset_1(esk5_3(esk1_0,X1,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,esk4_0,esk3_0)
    | ~ r1_lattice3(esk1_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r2_lattice3(esk1_0,esk4_0,esk2_0)
    | m1_subset_1(esk5_3(esk1_0,esk4_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk4_0,esk2_0),u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk3_0)
    | m1_subset_1(esk6_3(esk1_0,X1,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_9])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ v4_orders_2(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ m1_subset_1(X31,u1_struct_0(X28))
      | ~ r1_orders_2(X28,X29,X30)
      | ~ r1_orders_2(X28,X30,X31)
      | r1_orders_2(X28,X29,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk2_0)
    | m1_subset_1(esk5_3(esk1_0,esk4_0,esk2_0),u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_8]),c_0_9])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_3(esk1_0,esk4_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk3_0),X1)
    | r2_lattice3(esk1_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_15]),c_0_9])])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk2_0)
    | m1_subset_1(esk5_3(esk1_0,esk4_0,esk2_0),u1_struct_0(esk1_0))
    | ~ r2_hidden(esk6_3(esk1_0,esk4_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,esk4_0,esk3_0),esk4_0)
    | m1_subset_1(esk5_3(esk1_0,esk4_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,negated_conjecture,
    ( r1_lattice3(esk1_0,esk4_0,esk3_0)
    | ~ r2_lattice3(esk1_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_15]),c_0_8]),c_0_9]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk2_0)
    | m1_subset_1(esk5_3(esk1_0,esk4_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,esk2_0),X1)
    | r1_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_8]),c_0_9])])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_36,negated_conjecture,
    ( r1_lattice3(esk1_0,esk4_0,esk3_0)
    | m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_37,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk3_0)
    | m1_subset_1(esk5_3(esk1_0,esk4_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk4_0,esk2_0),esk4_0)
    | ~ r2_lattice3(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,X1)
    | m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15]),c_0_9])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk4_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_15]),c_0_9])]),c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk4_0,esk2_0),esk4_0)
    | m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk5_3(esk1_0,esk4_0,esk2_0))
    | m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk5_3(esk1_0,esk4_0,esk2_0))
    | m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_43]),c_0_41]),c_0_15]),c_0_9]),c_0_27])])).

cnf(c_0_45,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk5_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk5_3(esk1_0,esk4_0,esk2_0))
    | m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_26]),c_0_8])])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk1_0,esk4_0,esk2_0)
    | r1_lattice3(esk1_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_48,negated_conjecture,
    ( r1_lattice3(esk1_0,esk4_0,esk2_0)
    | m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_8]),c_0_9])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk4_0,esk2_0),esk4_0)
    | r2_lattice3(esk1_0,esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk1_0,esk4_0,esk3_0)
    | r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_47]),c_0_8]),c_0_9])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_3(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_48]),c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,esk4_0,esk3_0),esk4_0)
    | r1_lattice3(esk1_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk4_0,esk2_0),esk4_0)
    | r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_49]),c_0_8]),c_0_9])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,esk4_0,esk3_0),esk4_0)
    | r2_hidden(esk5_3(esk1_0,esk4_0,esk2_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( r1_lattice3(esk1_0,esk4_0,esk3_0)
    | r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk4_0,esk2_0),esk4_0)
    | r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_51]),c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_orders_2(esk1_0,esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_55]),c_0_15]),c_0_9])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk4_0,esk2_0),esk4_0)
    | r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_56]),c_0_51])])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk5_3(esk1_0,esk4_0,esk2_0))
    | r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ r2_hidden(esk5_3(esk1_0,esk4_0,esk2_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_41])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk4_0,esk2_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_58]),c_0_15]),c_0_9])]),c_0_39])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_orders_2(esk1_0,esk3_0,esk5_3(esk1_0,esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk5_3(esk1_0,esk4_0,esk2_0))
    | r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_61]),c_0_51])])).

cnf(c_0_63,negated_conjecture,
    ( r2_lattice3(esk1_0,esk4_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk5_3(esk1_0,esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_62]),c_0_15]),c_0_9])])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattice3(esk1_0,esk4_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk5_3(esk1_0,esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk5_3(esk1_0,esk4_0,esk2_0))
    | r1_orders_2(esk1_0,esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_64]),c_0_15]),c_0_9])])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk5_3(esk1_0,esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_41]),c_0_60])])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk5_3(esk1_0,esk4_0,esk2_0))
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_66]),c_0_41]),c_0_15]),c_0_9]),c_0_27])])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk5_3(esk1_0,esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_26]),c_0_8])])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattice3(esk1_0,esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_68]),c_0_8]),c_0_9])])).

cnf(c_0_70,negated_conjecture,
    ( r2_lattice3(esk1_0,esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_69])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_69])])).

cnf(c_0_72,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_70]),c_0_8]),c_0_9])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,esk4_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_24])).

cnf(c_0_74,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_51]),c_0_73])])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(esk1_0,esk6_3(esk1_0,esk4_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_74]),c_0_51])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_75]),c_0_15]),c_0_9])]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
