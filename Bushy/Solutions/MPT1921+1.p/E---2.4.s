%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t19_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   29 (  46 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  109 ( 171 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_yellow_6,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_6(X3,X1,X2)
             => r1_tarski(u1_struct_0(X3),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t19_yellow_6.p',t19_yellow_6)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t19_yellow_6.p',d13_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t19_yellow_6.p',dt_m1_yellow_0)).

fof(d8_yellow_6,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( l1_waybel_0(X3,X1)
             => ( m1_yellow_6(X3,X1,X2)
              <=> ( m1_yellow_0(X3,X2)
                  & u1_waybel_0(X1,X3) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t19_yellow_6.p',d8_yellow_6)).

fof(dt_m1_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m1_yellow_6(X3,X1,X2)
         => l1_waybel_0(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t19_yellow_6.p',dt_m1_yellow_6)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t19_yellow_6.p',dt_l1_waybel_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_waybel_0(X2,X1)
           => ! [X3] :
                ( m1_yellow_6(X3,X1,X2)
               => r1_tarski(u1_struct_0(X3),u1_struct_0(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_yellow_6])).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X24,X25] :
      ( ~ l1_orders_2(X24)
      | ~ m1_yellow_0(X25,X24)
      | l1_orders_2(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ( m1_yellow_0(X14,X13)
        | ~ m1_yellow_6(X14,X12,X13)
        | ~ l1_waybel_0(X14,X12)
        | ~ l1_waybel_0(X13,X12)
        | ~ l1_struct_0(X12) )
      & ( u1_waybel_0(X12,X14) = k2_partfun1(u1_struct_0(X13),u1_struct_0(X12),u1_waybel_0(X12,X13),u1_struct_0(X14))
        | ~ m1_yellow_6(X14,X12,X13)
        | ~ l1_waybel_0(X14,X12)
        | ~ l1_waybel_0(X13,X12)
        | ~ l1_struct_0(X12) )
      & ( ~ m1_yellow_0(X14,X13)
        | u1_waybel_0(X12,X14) != k2_partfun1(u1_struct_0(X13),u1_struct_0(X12),u1_waybel_0(X12,X13),u1_struct_0(X14))
        | m1_yellow_6(X14,X12,X13)
        | ~ l1_waybel_0(X14,X12)
        | ~ l1_waybel_0(X13,X12)
        | ~ l1_struct_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).

fof(c_0_10,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_struct_0(X26)
      | ~ l1_waybel_0(X27,X26)
      | ~ m1_yellow_6(X28,X26,X27)
      | l1_waybel_0(X28,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).

fof(c_0_11,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & m1_yellow_6(esk3_0,esk1_0,esk2_0)
    & ~ r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_12,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( ~ m1_yellow_0(esk3_0,esk2_0)
    | ~ l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

fof(c_0_24,plain,(
    ! [X22,X23] :
      ( ~ l1_struct_0(X22)
      | ~ l1_waybel_0(X23,X22)
      | l1_orders_2(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_25,negated_conjecture,
    ( ~ l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_26,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( ~ l1_waybel_0(esk2_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_20]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
