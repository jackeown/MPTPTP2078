%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t7_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:48 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   48 (1131 expanded)
%              Number of clauses        :   39 ( 472 expanded)
%              Number of leaves         :    4 ( 251 expanded)
%              Depth                    :   14
%              Number of atoms          :  254 (16974 expanded)
%              Number of equality atoms :   17 ( 524 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   67 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t7_yellow_0.p',t7_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t7_yellow_0.p',d9_lattice3)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t7_yellow_0.p',d1_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t7_yellow_0.p',d8_lattice3)).

fof(c_0_4,negated_conjecture,(
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

fof(c_0_5,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X23)
        | r1_orders_2(X22,X25,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk6_3(X22,X23,X24),u1_struct_0(X22))
        | r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk6_3(X22,X23,X24),X23)
        | r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,esk6_3(X22,X23,X24),X24)
        | r2_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_6,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) )
    & ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r1_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
      | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
      | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk4_2(X14,X15),X15)
        | esk4_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk4_2(X14,X15),X15)
        | esk4_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r1_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_hidden(X20,X18)
        | r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_3(X17,X18,X19),u1_struct_0(X17))
        | r1_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk5_3(X17,X18,X19),X18)
        | r1_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X19,esk5_3(X17,X18,X19))
        | r1_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_9,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,X1)
    | ~ r2_hidden(esk3_0,X2)
    | ~ r2_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).

cnf(c_0_16,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r2_hidden(esk3_0,X2)
    | ~ r1_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_10]),c_0_11])])).

cnf(c_0_17,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,X1)
    | ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk6_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk2_0),X1)
    | r2_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk5_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,esk2_0),X1)
    | r1_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_18]),c_0_11])])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,esk6_3(esk1_0,X1,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_11])])).

cnf(c_0_33,negated_conjecture,
    ( esk6_3(esk1_0,k1_tarski(X1),esk2_0) = X1
    | r2_lattice3(esk1_0,k1_tarski(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
    | ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk5_3(esk1_0,X1,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_11])])).

cnf(c_0_37,negated_conjecture,
    ( esk5_3(esk1_0,k1_tarski(X1),esk2_0) = X1
    | r1_lattice3(esk1_0,k1_tarski(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(esk1_0,k1_tarski(X1),esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r1_lattice3(esk1_0,k1_tarski(X1),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_43,negated_conjecture,
    ( r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
    | ~ r1_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,k1_tarski(esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_41])]),c_0_43])]),c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_41])]),c_0_43])]),c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_46]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
