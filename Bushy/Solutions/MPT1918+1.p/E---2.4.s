%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t16_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 122 expanded)
%              Number of clauses        :   22 (  47 expanded)
%              Number of leaves         :    4 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 423 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t16_yellow_6.p',d13_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t16_yellow_6.p',dt_m1_yellow_0)).

fof(t16_yellow_6,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_0(X3,X2)
             => m1_yellow_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t16_yellow_6.p',t16_yellow_6)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t16_yellow_6.p',t1_xboole_1)).

fof(c_0_4,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(u1_struct_0(X11),u1_struct_0(X10))
        | ~ m1_yellow_0(X11,X10)
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) )
      & ( r1_tarski(u1_orders_2(X11),u1_orders_2(X10))
        | ~ m1_yellow_0(X11,X10)
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_tarski(u1_struct_0(X11),u1_struct_0(X10))
        | ~ r1_tarski(u1_orders_2(X11),u1_orders_2(X10))
        | m1_yellow_0(X11,X10)
        | ~ l1_orders_2(X11)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

fof(c_0_5,plain,(
    ! [X13,X14] :
      ( ~ l1_orders_2(X13)
      | ~ m1_yellow_0(X14,X13)
      | l1_orders_2(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_yellow_0(X2,X1)
           => ! [X3] :
                ( m1_yellow_0(X3,X2)
               => m1_yellow_0(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_yellow_6])).

cnf(c_0_7,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & m1_yellow_0(esk3_0,esk2_0)
    & ~ m1_yellow_0(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(X31,X32)
      | ~ r1_tarski(X32,X33)
      | r1_tarski(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_11,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_12]),c_0_13])])).

cnf(c_0_19,plain,
    ( r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_14,c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_17]),c_0_18])])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(u1_orders_2(esk2_0),u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_12]),c_0_13])])).

cnf(c_0_23,plain,
    ( m1_yellow_0(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_17]),c_0_18])])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_yellow_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(X1,u1_orders_2(esk1_0))
    | ~ r1_tarski(X1,u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(u1_orders_2(esk3_0),u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_18])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(u1_orders_2(esk3_0),u1_orders_2(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_13]),c_0_25])]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
