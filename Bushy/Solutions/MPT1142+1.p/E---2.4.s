%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t32_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:19 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 805 expanded)
%              Number of clauses        :   30 ( 277 expanded)
%              Number of leaves         :    4 ( 188 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 (6944 expanded)
%              Number of equality atoms :   14 ( 132 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_orders_2,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( ( r2_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X3,X4) )
                      | ( r1_orders_2(X1,X2,X3)
                        & r2_orders_2(X1,X3,X4) ) )
                   => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t32_orders_2.p',t32_orders_2)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t32_orders_2.p',d10_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/orders_2__t32_orders_2.p',t26_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/orders_2__t32_orders_2.p',t25_orders_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( ( r2_orders_2(X1,X2,X3)
                          & r1_orders_2(X1,X3,X4) )
                        | ( r1_orders_2(X1,X2,X3)
                          & r2_orders_2(X1,X3,X4) ) )
                     => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_orders_2])).

fof(c_0_5,plain,(
    ! [X9,X10,X11] :
      ( ( r1_orders_2(X9,X10,X11)
        | ~ r2_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( X10 != X11
        | ~ r2_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,X10,X11)
        | X10 = X11
        | r2_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_6,negated_conjecture,
    ( v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r2_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( r2_orders_2(esk1_0,esk3_0,esk4_0)
      | r2_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_orders_2(esk1_0,esk3_0,esk4_0) )
    & ( r2_orders_2(esk1_0,esk3_0,esk4_0)
      | r1_orders_2(esk1_0,esk3_0,esk4_0) )
    & ~ r2_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ v4_orders_2(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ r1_orders_2(X23,X24,X25)
      | ~ r1_orders_2(X23,X25,X26)
      | r1_orders_2(X23,X24,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( X1 = esk4_0
    | r2_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_18,plain,(
    ! [X20,X21,X22] :
      ( ~ v5_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | ~ r1_orders_2(X20,X21,X22)
      | ~ r1_orders_2(X20,X22,X21)
      | X21 = X22 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 = esk2_0
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,X2,esk4_0)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9]),c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r2_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_9])])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | ~ r2_orders_2(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_8]),c_0_9])])).

cnf(c_0_24,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk4_0)
    | r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( esk4_0 = esk2_0
    | ~ r1_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13])])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_13])])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17])])).

cnf(c_0_30,negated_conjecture,
    ( X1 = esk3_0
    | ~ r1_orders_2(esk1_0,esk3_0,X1)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_9]),c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_17])])).

cnf(c_0_32,negated_conjecture,
    ( esk2_0 = esk3_0
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_13])])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk4_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_31]),c_0_35]),c_0_35])]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
